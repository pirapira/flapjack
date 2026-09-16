import Flapjack.RiscV.WordExpressionFlatten

/-!
# Word instruction selection for shared-memory addresses

Cake's `word_inst$inst_select` receives one fixed fresh temporary per
function.  For `ShareInst` it materializes the address into that temporary
and leaves a small `base + immediate` form when the offset fits.  The old
Flapjack boundary passed the expression tree directly to Word-to-Stack,
which is semantically usable but emits a different register sequence.
-/

namespace Flapjack.RiscV

open Flapjack

/-! The source selector is shared by the Nat-facing probes and by the
    concrete RISC-V `Word width` pipeline.  The latter must make the same
    target-dependent immediate decisions as Cake's `asm_config.valid_imm` and
    must distinguish an out-of-range constant shift from a selector that has
    no width information. -/

inductive WordShiftImmediate where
  | unsupported
  | valid (amount : Nat)
  | outOfRange
  deriving DecidableEq, Repr

class WordInstSelectImmediate (α : Type u) where
  validBinOpImmediate : BinOp → α → Bool
  shiftImmediate : α → WordShiftImmediate

instance : WordInstSelectImmediate Nat where
  validBinOpImmediate _ _ := false
  shiftImmediate _ := .unsupported

instance : WordInstSelectImmediate (BitVec width) where
  validBinOpImmediate operator value :=
    let n := value.toNat
    match operator with
    | .sub => n < 2 ^ 11
    | .add | .and | .or | .xor =>
        n < 2 ^ 11 || n ≥ 2 ^ width - 2 ^ 11
  shiftImmediate value :=
    if value.toNat < width then
      .valid value.toNat
    else
      .outOfRange

def wordInstSelectMaximum : List Nat → Nat
  | [] => 0
  | value :: values => max value (wordInstSelectMaximum values)
termination_by values => sizeOf values
decreasing_by all_goals decreasing_trivial

/- A local sequence join keeps the pass in the same right-associated shape as
`wordFlattenProgram`, without depending on the dead-code pass. -/
def wordDeadSelectSeq (first second : WordProg α) : WordProg α :=
  match first, second with
  | .skip, program => program
  | program, .skip => program
  | _, _ => .seq first second

/-! Cake's `pull_exp` and `flatten_exp` are observable before the allocator.
    `pull_ops` accumulates operands on the left, `optimize_consts` reverses the
    partitioned lists, and `flatten_exp` rebuilds an n-ary operation as a
    head-last binary tree.  Subtraction is the
    important exception: Cake handles it with `convert_sub` and never feeds
    it through the associative operand collector.  In particular, applying
    `pull_ops` to `Sub [x, y]` would incorrectly turn the expression into
    `Sub [y, x]`.  Keeping these cases explicit preserves the source operand
    order that feeds Cake's move preferences and clash graph. -/

def wordInstPullOps (operator : BinOp) :
    List (WordExp α) → List (WordExp α) → List (WordExp α)
  | [], accumulated => accumulated
  | expression :: expressions, accumulated =>
      match expression with
      | .op nested args =>
          if nested = operator then
            wordInstPullOps operator expressions (args ++ accumulated)
          else
            wordInstPullOps operator expressions (expression :: accumulated)
      | _ => wordInstPullOps operator expressions (expression :: accumulated)
termination_by expressions _ => sizeOf expressions
decreasing_by all_goals decreasing_trivial

def wordInstIsConstant : WordExp α → Bool
  | .const _ => true
  | _ => false

/-! Cake's `optimize_consts` folds the constant operands of an associative
    operation into a single constant and places it at the front of its
    (already `pull_ops`-reversed) operand list, and `flatten_exp` then moves
    that constant back to the last position.  The composition therefore keeps
    the non-constant operands in the partition order and puts the folded
    constant at the end.  Flapjack represents the same normal form directly:
    constants go last, which is what Cake's `inst_select_exp` immediate
    (`Const` as the second operand) case expects.  `reduce_const` drops the
    folded identity `0w` for `Add`, `Or` and `Xor`, and collapses a zero fold
    to `Const 0w` for `And` (HOL probe labels `optimize_consts_or_zero`,
    `optimize_consts_xor_zero`, `optimize_consts_and_zero`, `norm_or_zero`,
    `norm_and_zero`), so the zero cases are reproduced here.  Folding
    *non-zero* constants for `Or`, `Xor` and `And` needs the operator
    semantics, which this module (core type classes only, no Mathlib) cannot
    assume, and `op_consts` for empty operand lists remains a separate gap. -/
def wordInstConstantValue : WordExp α → Option α
  | .const value => some value
  | _ => none

def wordInstConstantsToEnd [Add α] [DecidableEq α] [OfNat α 0]
    (operator : BinOp) (expressions : List (WordExp α)) : List (WordExp α) :=
  let constants := expressions.filterMap wordInstConstantValue
  let others := expressions.filter (fun expression => !wordInstIsConstant expression)
  match constants with
  | [] => expressions.reverse
  | _ =>
      match operator with
      | .add =>
          -- Cake's `optimize_consts` folds the constant operands with `word_op`
          -- and `reduce_const` drops the result when it is the identity `0`, so
          -- `[Const 0; x]` normalizes to `[x]` and `[Const 0]` to `[Const 0]`.
          let folded := constants.foldr (fun value rest => value + rest) 0
          if folded = 0 then
            match others with
            | [] => [.const 0]
            | [single] => [single]
            | _ => others.reverse
          else
            [.const folded] ++ others.reverse
      | .or | .xor =>
          -- `reduce_const` drops a zero fold for `Or`/`Xor` exactly as for
          -- `Add`; only the all-zero fold is decidable without the operator.
          if constants.all (fun value => value = 0) then
            match others with
            | [] => [.const 0]
            | [single] => [single]
            | _ => others.reverse
          else
            constants.map (fun value => .const value) ++ others.reverse
      | .and =>
          -- `reduce_const And 0w rest = Const 0w` collapses the whole
          -- expression; a non-zero fold keeps the constant last.
          if constants.all (fun value => value = 0) then
            [.const 0]
          else
            constants.map (fun value => .const value) ++ others.reverse
      | _ => constants.map (fun value => .const value) ++ others.reverse

def wordInstConvertSub [Sub α] [OfNat α 0] : List (WordExp α) → WordExp α
  | [.const left, .const right] => .const (left - right)
  | [expression, .const value] => .op .add [.const (0 - value), expression]
  | expressions => .op .sub expressions

def wordInstPullExp [Sub α] [Add α] [DecidableEq α] [OfNat α 0] : WordExp α → WordExp α
  | .op operator [] => .op operator []
  | .op _ [expression] => wordInstPullExp expression
  | .op .sub expressions =>
      wordInstConvertSub (expressions.map wordInstPullExp)
  | .op operator expressions =>
      let expressions := expressions.map wordInstPullExp
      .op operator (wordInstConstantsToEnd operator (wordInstPullOps operator expressions []))
  | .load address => .load (wordInstPullExp address)
  | .shift operator left right =>
      .shift operator (wordInstPullExp left) (wordInstPullExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordInstFlattenExp : WordExp α → WordExp α
  /- `flatten_exp` (`word_instScript.sml`) matches `Op Sub exps` before every
     other `Op` clause and maps over the operands, keeping their order.  The
     clause below it rewrites `Op op (x::xs)` to `Op op [.. xs; x]`, which is
     only sound for the commutative operators; applying it to `Sub` turns
     `a - b` into `b - a`.  Without this clause `fun 1 ab(1 a, 1 b) { return
     a - b; }` compiled to `sub a0, a1, a0` where Cake emits
     `sub a0, a0, a1`.  Matching Cake's clause order matters beyond the
     two-operand case: a one-element `Op Sub [e]` has to stay
     `Op Sub [flatten_exp e]` rather than collapse through the `Op _ [x]`
     clause. -/
  | .op .sub expressions => .op .sub (expressions.map wordInstFlattenExp)
  | .op operator [] => .op operator []
  | .op _ [expression] => wordInstFlattenExp expression
  | .op operator (expression :: expressions) =>
      .op operator
        [ wordInstFlattenExp (.op operator expressions)
        , wordInstFlattenExp expression ]
  | .load address => .load (wordInstFlattenExp address)
  | .shift operator left right =>
      .shift operator (wordInstFlattenExp left) (wordInstFlattenExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordInstNormalizeExp [Sub α] [Add α] [DecidableEq α] [OfNat α 0] (expression : WordExp α) : WordExp α :=
  wordInstFlattenExp (wordInstPullExp expression)

def wordInstSelectAtom [Sub α] [Add α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α]
    (temp : Nat) : WordExp α → WordProg α × WordExp α
  | .const value => (.inst (.const temp value), .var temp)
  | .var name => (.move 0 [(temp, name)], .var temp)
  | .lookup store => (.get temp store, .var temp)
  | .load address =>
      /- `inst_select_exp c tar temp (Load exp)` (`word_instScript.sml:234-245`)
         checks the address for `Op Add [exp'; Const w]` and keeps `w` in the
         `Addr temp w` it emits.  Selecting the address with the ordinary atom
         selector folds that `w` into an `addi` instead, which costs an extra
         instruction and loses the offset the Word-to-Stack pass would have
         fused: `calculate_total_blob_gas` in the stateless-pancaketh guest
         came out as `addi a0, a0, 264; ld a0, 0(a0)` where Cake emits
         `ld a0, 264(a0)`.  The statement-level load at
         `wordInstSelectProgram` already selects its address this way; do the
         same here so an expression-level load agrees with it. -/
      let (prelude, selectedAddress) :=
        let addressImmediate : WordInstSelectImmediate α := inferInstance
        letI : WordInstSelectImmediate α :=
          { validBinOpImmediate := fun _ _ => false
            /- Cake's address path suppresses arithmetic immediates so that
               Addr offsets remain visible to Word-to-Stack, but its nested
               Shift case still sees the ordinary target configuration.  In
               particular, flatten_exp deliberately leaves a shift amount
               Const untouched, so (i * 8) must become slli rather than a
               materialized shift-register pair. -/
            shiftImmediate := addressImmediate.shiftImmediate }
        wordInstSelectAtom temp address
      match selectedAddress with
      | .var address =>
          /- Cake's `inst_select_exp` lowers every expression-level load to a
             genuine `Mem Load` instruction.  Keeping this as an `Assign`
             leaves the load invisible to `word_cse`, so repeated loads cannot
             share the first result and the final code grows relative to Cake.
             The selected address is normally the returned temporary, just as
             in Cake's `Addr temp 0w` case. -/
          (wordDeadSelectSeq prelude (.inst (.mem .load temp address)), .var temp)
      | _ =>
          /- Address selectors intentionally retain an unfused base-plus-
             offset expression for the later Word-to-Stack offset handling.
             Preserve that fallback instead of pretending that `temp` holds
             the complete address. -/
          (wordDeadSelectSeq prelude (.assign temp (.load selectedAddress)), .var temp)
  | .op .add [left, .const value] =>
      let (prelude, selectedLeft) := wordInstSelectAtom temp left
      match selectedLeft with
      | .var left =>
          if WordInstSelectImmediate.validBinOpImmediate .add value then
            (wordDeadSelectSeq prelude
              (.inst (.arith (.binOp .add temp left (.imm value)))), .var temp)
          else if WordInstSelectImmediate.validBinOpImmediate .sub (0 - value) then
            (wordDeadSelectSeq prelude
              (.inst (.arith (.binOp .sub temp left (.imm (0 - value))))), .var temp)
          else
            (prelude, .op .add [selectedLeft, .const value])
      | _ => (prelude, .op .add [selectedLeft, .const value])
  | .op operator [left, right] =>
      let (leftPrelude, _) := wordInstSelectAtom temp left
      let (rightPrelude, _) := wordInstSelectAtom (temp + 1) right
      let code := wordDeadSelectSeq leftPrelude rightPrelude
      let generic :=
        (wordDeadSelectSeq code
          (.inst (.arith (.binOp operator temp temp (.reg (temp + 1))))), .var temp)
      match operator, left, right with
      | .add, .lookup .currHeap,
          .shift .lsl (.lookup .heapLength) (.const value) =>
          if value = (1 : α) then
            (.seq (.get temp .heapLength)
              (.seq (.inst (.arith (.shift .lsl temp temp (.imm (1 : α)))))
                (.opCurrHeap .add temp temp)), .var temp)
          else generic
      | .add, .shift .lsl (.lookup .heapLength) (.const value),
          .lookup .currHeap =>
          if value = (1 : α) then
            (.seq (.get temp .heapLength)
              (.seq (.inst (.arith (.shift .lsl temp temp (.imm (1 : α)))))
                (.opCurrHeap .add temp temp)), .var temp)
          else generic
      | _, _, _ => generic
  | .shift operator left (.const value) =>
      let (leftPrelude, selectedLeft) := wordInstSelectAtom temp left
      match selectedLeft, WordInstSelectImmediate.shiftImmediate value with
      | .var left, .valid amount =>
          if amount = 0 then
            (leftPrelude, .var temp)
          else
            (wordDeadSelectSeq leftPrelude
              (.inst (.arith (.shift operator temp left (.imm value)))), .var temp)
      | _, .outOfRange =>
          (.inst (.const temp 0), .var temp)
      | selectedLeft, _ =>
          /- `wordInstSelectAtom` does not always leave the whole left operand
             in `temp`: with binary-operation immediates disabled -- which is
             how addresses are selected -- `base + c` comes back as the
             expression `.op .add [.var temp, .const c]`, with only `base` in
             `temp`.  Shifting `.var temp` therefore dropped the `+ c`, and
             `lds 1 (1000 + (k - 1) * 8)` was compiled as if it were
             `lds 1 (1000 + k * 8)`.  Shift what the selector returned.

             Cake reaches this shape differently: `inst_select_exp c tar temp
             (Shift sh exp n)` (`word_instScript.sml`) selects `exp` into
             `temp` with the ordinary configuration and then shifts that
             register by the immediate, so it emits one fewer instruction
             here.  Materialising `selectedLeft` into `temp` to match makes
             `wordToStack` reject the result on the guest's
             `bls_g2_msm_discount`, so the expression carrier stays and the
             remaining instruction-count difference is left alone. -/
          let rightPrelude : WordProg α :=
            .inst (.const (temp + 1) value)
          let code := wordDeadSelectSeq leftPrelude rightPrelude
          (wordDeadSelectSeq code
            (.assign temp (.shift operator selectedLeft (.var (temp + 1)))), .var temp)

  | .shift operator left right =>
      let (leftPrelude, _) := wordInstSelectAtom temp left
      let (rightPrelude, _) := wordInstSelectAtom (temp + 1) right
      let code := wordDeadSelectSeq leftPrelude rightPrelude
      (wordDeadSelectSeq code
        (.inst (.arith (.shift operator temp temp (.reg (temp + 1))))), .var temp)
  | expression => (.assign temp expression, .var temp)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | decreasing_trivial | (simp [sizeOf] <;> omega)

/-! Address expressions are selected by Cake's generic `inst_select_exp` path.
    In particular, a base-plus-offset address must remain an expression so the
    later Word-to-Stack pass can fuse the offset into the memory instruction.
    Immediate arithmetic is still selected for ordinary assignments, but must
    not change this address shape. -/
def wordInstSelectAddressAtom [Sub α] [Add α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α]
    (temp : Nat) (expression : WordExp α) : WordProg α × WordExp α :=
  let addressImmediate : WordInstSelectImmediate α := inferInstance
  letI : WordInstSelectImmediate α :=
    { validBinOpImmediate := fun _ _ => false
      /- Address arithmetic must remain available for Addr-offset fusion,
         but nested shifts follow the target configuration just as in Cake's
         inst_select_exp. -/
      shiftImmediate := addressImmediate.shiftImmediate }
  wordInstSelectAtom temp expression

def wordInstSelectProgram [Sub α] [Add α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α]
    (temp : Nat) : WordProg α → WordProg α
  | .seq first second =>
      wordDeadSelectSeq (wordInstSelectProgram temp first)
        (wordInstSelectProgram temp second)
  | .shareInst operator name address =>
      let (prelude, address) :=
        wordInstSelectAddressAtom temp (wordInstNormalizeExp address)
      wordDeadSelectSeq prelude (.shareInst operator name address)
  | .assign destination value =>
      let value := wordInstNormalizeExp value
      match value with
      | .lookup store => .get destination store
      | .load address =>
          let (prelude, address) := wordInstSelectAddressAtom temp address
          match address with
          | .var address =>
              wordDeadSelectSeq prelude (.inst (.mem .load destination address))
          | _ => wordDeadSelectSeq prelude (.assign destination (.load address))
      | .op operator [left, .const value] =>
          let (prelude, left) := wordInstSelectAtom temp left
          match left with
          | .var left =>
              if WordInstSelectImmediate.validBinOpImmediate operator value then
                wordDeadSelectSeq prelude
                  (.inst (.arith (.binOp operator destination left (.imm value))))
              else if operator = .add &&
                  WordInstSelectImmediate.validBinOpImmediate .sub (0 - value) then
                wordDeadSelectSeq prelude
                  (.inst (.arith (.binOp .sub destination left (.imm (0 - value)))))
              else
                wordDeadSelectSeq prelude
                  (.assign destination (.op operator [.var left, .const value]))
          | _ => wordDeadSelectSeq prelude
              (.assign destination (.op operator [left, .const value]))
      | .shift operator left (.const value) =>
          let (prelude, left) := wordInstSelectAtom temp left
          match left, WordInstSelectImmediate.shiftImmediate value with
          | .var left, .valid amount =>
              if amount = 0 then
                wordDeadSelectSeq prelude (.move 0 [(destination, left)])
              else
                wordDeadSelectSeq prelude
                  (.inst (.arith (.shift operator destination left (.imm value))))
          | _, .outOfRange => .inst (.const destination 0)
          | _, _ => .assign destination (.shift operator left (.const value))
      | .shift operator left right =>
          let (leftPrelude, left) := wordInstSelectAtom temp left
          let (rightPrelude, right) := wordInstSelectAtom (temp + 1) right
          let body :=
            match left, right with
            | .var left, .var right =>
                .inst (.arith (.shift operator destination left (.reg right)))
            | _, _ => .assign destination (.shift operator left right)
          wordDeadSelectSeq leftPrelude
            (wordDeadSelectSeq rightPrelude body)
      | .const value => .inst (.const destination value)
      | .op operator [left, right] =>
          let (leftPrelude, left) := wordInstSelectAtom temp left
          let (rightPrelude, right) := wordInstSelectAtom (temp + 1) right
          /- Cake's `inst_select_exp` emits an operation whose operands are the
             register numbers the materialising preludes wrote, not rewritable
             expressions.  Keeping that carrier is what stops expression-level
             passes (copy propagation in particular) from folding the operand
             copies away; the allocation outcome is observable in the final
             bytes.  The immediates keep the expression form so that the
             instruction selector's constant folding is untouched. -/
          let body :=
            match left, right with
            | .var left, .var right =>
                .inst (.arith (.binOp operator destination left (.reg right)))
            | _, _ => .assign destination (.op operator [left, right])
          wordDeadSelectSeq leftPrelude
            (wordDeadSelectSeq rightPrelude body)
      | .var source => .move 0 [(destination, source)]
      | value => .assign destination value
  | .store address value =>
      let (prelude, address) :=
        wordInstSelectAddressAtom temp (wordInstNormalizeExp address)
      match address with
      | .var address =>
          /- Cake's selected Store is an actual WordLang Mem instruction
             addressed through the fresh temporary.  Keeping it as a
             structured WordProg.store lets copy propagation rewrite the
             address expression away, which changes the allocator-visible
             move shape. -/
          wordDeadSelectSeq prelude (.inst (.mem .store value address))
      | _ => wordDeadSelectSeq prelude (.store address value)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right
        (wordInstSelectProgram temp thenBranch)
        (wordInstSelectProgram temp elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordInstSelectProgram temp body) liveOut
  | .mustTerminate body => .mustTerminate (wordInstSelectProgram temp body)
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments none =>
      .call (some (destinations, cutsets,
        wordInstSelectProgram temp returnCode, returnLabel, entryLabel))
        target arguments none
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments (some (exception, body, handlerLabel, handlerEntryLabel)) =>
      .call (some (destinations, cutsets,
        wordInstSelectProgram temp returnCode, returnLabel, entryLabel))
        target arguments
        (some (exception, wordInstSelectProgram temp body,
          handlerLabel, handlerEntryLabel))
  | .call none target arguments none =>
      .call none target arguments none
  | .call none target arguments (some (exception, body, handlerLabel, handlerEntryLabel)) =>
      .call none target arguments
        (some (exception, wordInstSelectProgram temp body,
          handlerLabel, handlerEntryLabel))
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordInstSelectProgramFrom [Sub α] [Add α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α]
    (program : WordProg α) : WordProg α :=
  wordInstSelectProgram (wordInstSelectMaximum (wordProgVariables program) + 1) program

end Flapjack.RiscV
