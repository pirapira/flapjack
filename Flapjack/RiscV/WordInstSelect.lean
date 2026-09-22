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
  validSharedMemoryOffset : WordMemOp → α → Bool
  shiftImmediate : α → WordShiftImmediate
  negateImmediate : α → α
  /- The current allocator bridge has an established expression-shaped path
     for positive offset spill chains.  Negative RV offsets are the Cake
     shape whose direct `Addr` carrier is required by the parity corpus. -/
  negativeAddressOffset : α → Bool

/-! Cake's `op_consts` identity for an empty operation.  The source-facing
    Nat carrier models 64-bit Pancake words, while concrete callers use
    `BitVec width`; keeping the identity explicit avoids using unbounded Nat
    complement for the abstract carrier. -/
class WordInstSelectConstants (α : Type u) where
  andIdentity : α

instance : WordInstSelectConstants Nat where
  andIdentity := 2 ^ 64 - 1

instance (priority := 100) : WordInstSelectConstants (BitVec width) where
  andIdentity := ~~~(0 : BitVec width)

instance : WordInstSelectImmediate Nat where
  /- The source-facing pipeline carries RV64 words as `Nat` after the
     word-to-stack boundary.  This is not an unbounded integer target: the
     values are the bit patterns of 64-bit words, so use the same signed
     12-bit immediate test as the concrete `BitVec 64` instance. -/
  validBinOpImmediate operator value :=
    match operator with
    /- RISC-V's `valid_imm` is strict at the negative endpoint for Sub:
       `min12 < i <= max12`.  In the 64-bit word carrier this includes the
       bit patterns for -2047 through -1 as well as 0 through 2047. -/
    | .sub => value < 2 ^ 11 || value > 2 ^ 64 - 2 ^ 11
    | .add | .and | .or | .xor =>
        value < 2 ^ 11 || value ≥ 2 ^ 64 - 2 ^ 11
  validSharedMemoryOffset _operator value :=
    let fits := value < 2 ^ 11 || value ≥ 2 ^ 64 - 2 ^ 11
    fits
  shiftImmediate value :=
    if value < 64 then .valid value else .outOfRange
  negateImmediate value := (2 ^ 64 - value) % 2 ^ 64
  negativeAddressOffset value := value ≥ 2 ^ 63

instance : WordInstSelectImmediate (BitVec width) where
  validBinOpImmediate operator value :=
    let n := value.toNat
    match operator with
    | .sub => n < 2 ^ 11 || n > 2 ^ width - 2 ^ 11
    | .add | .and | .or | .xor =>
        n < 2 ^ 11 || n ≥ 2 ^ width - 2 ^ 11
  validSharedMemoryOffset _operator value :=
    let n := value.toNat
    let fits := n < 2 ^ 11 || n ≥ 2 ^ width - 2 ^ 11
    fits
  shiftImmediate value :=
    if value.toNat < width then
      .valid value.toNat
    else
      .outOfRange
  negateImmediate value := 0 - value
  negativeAddressOffset value := value.toNat ≥ 2 ^ (width - 1)

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
    `norm_and_zero`), so the zero cases are reproduced here.  `wordInstFoldConstants`
    uses the available `And`/`Or`/`Xor`/arithmetic operation classes for
    non-zero folds too.  Unlike the other operators, `And` folds its
    non-empty constant list from the first operand, so no all-ones identity
    is required; `op_consts` for empty operand lists is handled by
    `wordInstOpConstants` below. -/
def wordInstConstantValue : WordExp α → Option α
  | .const value => some value
  | _ => none

/-! `word_op`/`optimize_consts` from Cake's `word_inst` fold all constant
    operands before `flatten_exp` rebuilds the expression.  Keeping only the
    zero-identity cases here was enough for earlier fixtures, but left
    non-zero constant expressions such as `7 | 7` as an extra instruction.
    That extra instruction is observable in a call handler because it shifts
    every later SSA name and code section. -/
def wordInstFoldConstants [Add α] [Sub α] [AndOp α] [OrOp α]
    [HXor α α α] [OfNat α 0]
    (operator : BinOp) (values : List α) : Option α :=
  match operator, values with
  | .add, values => some (values.foldr (fun value rest => value + rest) 0)
  | .and, value :: values => some (values.foldl (fun acc value => acc &&& value) value)
  | .or, values => some (values.foldr (fun value rest => value ||| rest) 0)
  | .xor, values => some (values.foldr (fun value rest => value ^^^ rest) 0)
  | .sub, [left, right] => some (left - right)
  | _, _ => none

def wordInstConstantsToEnd [Add α] [Sub α] [AndOp α] [OrOp α]
    [HXor α α α] [DecidableEq α] [OfNat α 0]
    (operator : BinOp) (expressions : List (WordExp α)) : List (WordExp α) :=
  let constants := expressions.filterMap wordInstConstantValue
  let others := expressions.filter (fun expression => !wordInstIsConstant expression)
  match constants with
  | [] => expressions.reverse
  | _ =>
      match wordInstFoldConstants operator constants with
      | none => constants.map (fun value => .const value) ++ others.reverse
      | some folded =>
          if folded = 0 then
            match operator with
            | .add | .or | .xor =>
                match others with
                | [] => [.const folded]
                | [single] => [single]
                | _ => others.reverse
            | .and => [.const folded]
            | _ => [.const folded] ++ others.reverse
          else
            [.const folded] ++ others.reverse

def wordInstConvertSub [Sub α] [OfNat α 0] : List (WordExp α) → WordExp α
  | [.const left, .const right] => .const (left - right)
  | [expression, .const value] => .op .add [.const (0 - value), expression]
  | expressions => .op .sub expressions

def wordInstOpConstants [OfNat α 0] [WordInstSelectConstants α]
    (operator : BinOp) : WordExp α :=
  match operator with
  | .and => .const WordInstSelectConstants.andIdentity
  | _ => .const 0

def wordInstPullExp [Sub α] [Add α] [AndOp α] [OrOp α] [HXor α α α]
    [DecidableEq α] [OfNat α 0] [WordInstSelectConstants α] : WordExp α → WordExp α
  | .op operator [] => wordInstOpConstants operator
  | .op _ [expression] => wordInstPullExp expression
  | .op .sub expressions =>
      wordInstConvertSub (expressions.map wordInstPullExp)
  | .op operator expressions =>
      let expressions := expressions.map wordInstPullExp
      let normalized := wordInstConstantsToEnd operator
        (wordInstPullOps operator expressions [])
      match normalized with
      | [expression] =>
          match expression with
          | .const value => if value = 0 then expression else .op operator normalized
          | _ => expression
      | _ => .op operator normalized
  | .load address => .load (wordInstPullExp address)
  | .shift operator left right =>
      .shift operator (wordInstPullExp left) (wordInstPullExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordInstFlattenExp [WordInstSelectConstants α] [OfNat α 0] : WordExp α → WordExp α
  | .op .sub expressions =>
      -- Cake's `flatten_exp` preserves subtraction operands; the generic
      -- n-ary case below rebuilds an associative operation as
      -- `[flatten(rest), flatten(head)]`, which is valid for associative
      -- operators but reverses `Sub [left, right]`.
      .op .sub (expressions.map wordInstFlattenExp)
  | .op operator [] => wordInstOpConstants operator
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

def wordInstNormalizeExp [Sub α] [Add α] [AndOp α] [OrOp α] [HXor α α α]
    [DecidableEq α] [OfNat α 0] [WordInstSelectConstants α]
    (expression : WordExp α) : WordExp α :=
  wordInstFlattenExp (wordInstPullExp expression)

/-- Shared tail of `inst_select_exp`'s `Load` case: the selected address is
    normally the returned temporary, matching Cake's `Addr temp 0w`, and Cake
    lowers every expression-level load to a genuine `Mem Load` instruction.
    Keeping it as an `Assign` would leave the load invisible to `word_cse`, so
    repeated loads could not share the first result.  Valid base-plus-offset
    addresses retain their offset in the selected memory instruction; an
    out-of-range offset is materialized before a zero-offset load, matching
    `word_instScript.sml:234-245`. -/
def wordInstSelectLoadTail [WordInstSelectImmediate α] (temp : Nat) (prelude : WordProg α)
    (selectedAddress : WordExp α) : WordProg α × WordExp α :=
  match selectedAddress with
  | .op .add [.var address, .const offset] =>
      if WordInstSelectImmediate.validSharedMemoryOffset .load offset then
        (wordDeadSelectSeq prelude
          (.inst (.memOffset .load temp address offset)), .var temp)
      else
        let materialize := wordDeadSelectSeq prelude
          (.inst (.const (temp + 1) offset))
        let materialize := wordDeadSelectSeq materialize
          (.inst (.arith (.binOp .add temp temp (.reg (temp + 1)))))
        (wordDeadSelectSeq materialize
          (.inst (.mem .load temp temp)), .var temp)
  | .var address =>
      (wordDeadSelectSeq prelude (.inst (.mem .load temp address)), .var temp)
  | _ =>
      (wordDeadSelectSeq prelude (.inst (.mem .load temp temp)), .var temp)

def wordInstSelectAtom [Sub α] [Add α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α]
    (temp : Nat) : WordExp α → WordProg α × WordExp α
  | .const value => (.inst (.const temp value), .var temp)
  | .var name => (.move 0 [(temp, name)], .var temp)
  | .lookup store => (.get temp store, .var temp)
  | .load (.op .add [base, .const value]) =>
      /- `inst_select_exp c tar temp (Load exp)` (`word_instScript.sml:234-245`)
         checks the address for `Op Add [exp'; Const w]` and keeps `w` in the
         `Addr temp w` it emits, selecting only `exp'`.  Folding that `w` into
         an `addi` instead costs an extra instruction and loses the offset the
         Word-to-Stack pass would have fused: `calculate_total_blob_gas` in the
         stateless-pancaketh guest came out as `addi a0, a0, 264; ld a0, 0(a0)`
         where Cake emits `ld a0, 264(a0)`.  Note that Cake splits on the
         address shape and still selects `exp'` with the ordinary target
         configuration; suppressing immediates for the whole address would also
         reach nested subexpressions, where Cake selects `addi`/`slli`.

         Cake only takes this split when `addr_offset_ok c w` holds
         (`word_instScript.sml:237`); an out-of-range offset selects the whole
         address expression with `Addr temp 0w`.  For a CurrHeap base that
         matters: selecting the whole `Op Add [Lookup CurrHeap; Const w]`
         reaches Cake's `Const temp w; OpCurrHeap op temp temp` case, which
         keeps the dedicated CurrHeap register (`s10`) as the memory base.  The
         offset split would instead materialize CurrHeap into a temporary,
         emitting an extra `move` that Cake does not. -/
      if WordInstSelectImmediate.validSharedMemoryOffset .load value then
        let (prelude, selectedBase) := wordInstSelectAtom temp base
        wordInstSelectLoadTail temp prelude (.op .add [selectedBase, .const value])
      else
        let (prelude, selectedAddress) :=
          wordInstSelectAtom temp (.op .add [base, .const value])
        wordInstSelectLoadTail temp prelude selectedAddress
  | .load address =>
      let (prelude, selectedAddress) := wordInstSelectAtom temp address
      wordInstSelectLoadTail temp prelude selectedAddress
  | .op operator [.lookup .currHeap, .const value] =>
      /- Cake's `inst_select_exp` (`word_instScript.sml:246-251`) tests
         `is_Lookup_CurrHeap e1 ∧ op ≠ Sub` before the `e2 = Const w`
         immediate fold, so a CurrHeap left operand keeps Cake's
         `Const temp w; OpCurrHeap op temp temp` shape instead of folding
         the constant into an immediate.  `Sub` is excluded by that test and
         falls through to the ordinary immediate path. -/
      if operator = .sub then
        let prelude : WordProg α := .get temp .currHeap
        let materialized : WordProg α × WordExp α :=
          (wordDeadSelectSeq (wordDeadSelectSeq prelude (.inst (.const (temp + 1) value)))
            (.inst (.arith (.binOp operator temp temp (.reg (temp + 1))))), .var temp)
        if WordInstSelectImmediate.validBinOpImmediate operator value then
          (wordDeadSelectSeq prelude
            (.inst (.arith (.binOp operator temp temp (.imm value)))), .var temp)
        else materialized
      else
        (wordDeadSelectSeq (.inst (.const temp value))
          (.opCurrHeap operator temp temp), .var temp)
  | .op operator [left, .const value] =>
      /- `inst_select_exp c tar temp (Op op [e1; e2])` with `e2 = Const w`
         (`word_instScript.sml:252-275`) tests `c.valid_imm (INL op) w` for
         *every* operator, not only `Add`; the `Sub` retry with `-w` is the
         only `Add`-specific step, and the remaining case materializes `w`
         into `temp + 1`.  Restricting the immediate test to `Add` made a
         nested `x && 1w` emit `ori t, x0, 1; and d, x, t` where Cake emits
         `andi d, x, 1`, one instruction more per occurrence; the
         statement-level selector below already agreed with Cake.

         Address selection is handled separately by
         `wordInstSelectAddressAtom`, so ordinary out-of-range operations take
         Cake's `Const`/`Reg` materialization here. -/
      let (prelude, selectedLeft) := wordInstSelectAtom temp left
      let materialized : WordProg α × WordExp α :=
        (wordDeadSelectSeq (wordDeadSelectSeq prelude (.inst (.const (temp + 1) value)))
          (.inst (.arith (.binOp operator temp temp (.reg (temp + 1))))), .var temp)
      let normal :=
        match selectedLeft with
        | .var selected =>
            if WordInstSelectImmediate.validBinOpImmediate operator value then
              wordDeadSelectSeq prelude
                (.inst (.arith (.binOp operator temp selected (.imm value))))
            else if operator = .add &&
                WordInstSelectImmediate.validBinOpImmediate .sub
                  (WordInstSelectImmediate.negateImmediate value) then
              wordDeadSelectSeq prelude
                (.inst (.arith (.binOp .sub temp selected
                  (.imm (WordInstSelectImmediate.negateImmediate value)))))
            else materialized.1
        | _ => materialized.1
      match selectedLeft with
      | .var _selected =>
          match left with
          | .lookup .currHeap =>
              if operator = .sub then
                (normal, .var temp)
              else
                (wordDeadSelectSeq (.inst (.const temp value))
                  (.opCurrHeap operator temp temp), .var temp)
          | _ => (normal, .var temp)
      | _ =>
          (materialized.1, .var temp)
  | .op operator [left, right] =>
      let (leftPrelude, _) := wordInstSelectAtom temp left
      let (rightPrelude, _) := wordInstSelectAtom (temp + 1) right
      let (rightHeapPrelude, _) := wordInstSelectAtom temp right
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
      | _, _, .lookup .currHeap =>
          let (prelude, _) := wordInstSelectAtom temp left
          (wordDeadSelectSeq prelude (.opCurrHeap operator temp temp), .var temp)
      | _, .lookup .currHeap, _ =>
          if operator = .sub then
            generic
          else
            (wordDeadSelectSeq rightHeapPrelude
              (.opCurrHeap operator temp temp), .var temp)
      | _, _, _ => generic
  | .shift operator left (.const value) =>
      let (leftPrelude, selectedLeft) := wordInstSelectAtom temp left
      match selectedLeft, WordInstSelectImmediate.shiftImmediate value with
      | .var left, .valid amount =>
          if amount = 0 then
            /- Cake's `inst_select_exp` emits the final `Move 0 [tar,temp]`
               even when the shift selector was already called with
               `tar = temp`.  The self-copy is observable to SSA numbering
               and the allocator, so preserve it rather than simplifying it
               away at this boundary. -/
            (wordDeadSelectSeq leftPrelude (.move 0 [(temp, temp)]), .var temp)
          else
            (wordDeadSelectSeq leftPrelude
              (.inst (.arith (.shift operator temp left (.imm value)))), .var temp)
      | _, .outOfRange =>
          (.inst (.const temp 0), .var temp)
      | _, _ =>
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

/- Cake's `shiftImmediate` rejects amounts at or above the RV word width.
   The selector's source-faithful fallback is independent of the selected
   left operand: it materializes the zero result in the current temporary. -/
theorem wordInstSelectAtom_nat_shift_outOfRange
    (temp : Nat) (operator : Shift) (left : WordExp Nat) (amount : Nat)
    (hamount : 64 ≤ amount) :
    wordInstSelectAtom (α := Nat) temp
        (.shift operator left (.const amount)) =
      (.inst (.const temp 0), .var temp) := by
  have hnot : ¬ amount < 64 := Nat.not_lt_of_ge hamount
  simp [wordInstSelectAtom, WordInstSelectImmediate.shiftImmediate, hnot]

/-! Address expressions are selected by Cake's generic `inst_select_exp` path.
    In particular, a base-plus-offset address must remain an expression so the
    later Word-to-Stack pass can fuse the offset into the memory instruction.
    Immediate arithmetic is still selected for ordinary assignments, but must
    not change this address shape. -/
def wordInstSelectAddressAtom [Sub α] [Add α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α]
    (temp : Nat) (expression : WordExp α) : WordProg α × WordExp α :=
  /- `inst_select_exp c tar temp (Load exp)` (`word_instScript.sml:234-245`)
     splits on the address shape once: an `Op Add [exp'; Const w]` keeps `w`
     for the `Addr temp w` it emits and selects only `exp'`, and every other
     address is selected whole.  Both recursive calls use the ordinary target
     configuration -- Cake has no second, immediate-suppressing config.  The
     distinction is observable for `base + ((k - 1) << 3)`: the subtraction
     and shift must stay `addi`/`slli`, while a final `base + constant` must
     stay an expression for the memory-offset fusion in Word-to-Stack. -/
  match expression with
  | .op .add [left, .const value] =>
      /- Cake splits on this shape only when `addr_offset_ok c w` holds
         (`word_instScript.sml:237`); otherwise it selects the whole address
         expression with `Addr temp 0w`.  Keeping the split for an out-of-range
         offset would materialize the base into a temporary instead of letting
         the `Op` case keep the dedicated CurrHeap register. -/
      if WordInstSelectImmediate.validSharedMemoryOffset .load value then
        let (prelude, selectedLeft) := wordInstSelectAtom temp left
        (prelude, .op .add [selectedLeft, .const value])
      else
        wordInstSelectAtom temp expression
  | _ => wordInstSelectAtom temp expression

/- Cake's `ShareInst` uses an `Addr base offset` only when the target
   memory encoding accepts that offset (`word_instScript.sml:409-418`).  The
   expression. -/
def wordInstSelectShareOffsetAllowed [WordInstSelectImmediate α]
    (_operator : WordMemOp) (offset : α) : Bool :=
  WordInstSelectImmediate.validSharedMemoryOffset _operator offset

/-! Cake-faithful standalone Store boundary.

`wordInstSelectProgram` retains the source-shaped positive-offset carrier for
the currently parity-green Word-to-Stack path.  This separate boundary mirrors
the `Store` clause of Cake's `inst_select_def`: a valid address offset is kept
in `Mem Store ... (Addr temp offset)`, while every other address is selected
into `temp` and emitted with a zero-offset memory instruction.  It is intended
for checked theorem/API clients until the downstream carrier integration can
be migrated without changing accepted artifacts. -/
def wordInstSelectStoreCake [Sub α] [Add α] [AndOp α] [OrOp α]
    [HXor α α α] [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α] [WordInstSelectConstants α]
    (temp : Nat) (address : WordExp α) (value : Nat) : WordProg α :=
  let address := wordInstNormalizeExp address
  match address with
  | .op .add [base, .const offset] =>
      if wordInstSelectShareOffsetAllowed .store offset then
        let (prelude, _) := wordInstSelectAtom temp base
        wordDeadSelectSeq prelude
          (.inst (.memOffset .store value temp offset))
      else
        let (prelude, _) := wordInstSelectAtom temp base
        let materialized :=
          .seq prelude
            (.seq (.inst (.const (temp + 1) offset))
              (.inst (.arith (.binOp .add temp temp (.reg (temp + 1))))))
        .seq materialized (.inst (.mem .store value temp))
  | _ =>
      let (prelude, _) := wordInstSelectAtom temp address
      wordDeadSelectSeq prelude (.inst (.mem .store value temp))

def wordInstSelectProgram [Sub α] [Add α] [AndOp α] [OrOp α] [HXor α α α]
    [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α] [WordInstSelectConstants α]
    (temp : Nat) : WordProg α → WordProg α
  | .seq first second =>
      wordDeadSelectSeq (wordInstSelectProgram temp first)
        (wordInstSelectProgram temp second)
  | .shareInst operator name address =>
      /- Cake's `ShareInst` selector keeps an address offset only when the
         corresponding load/store encoding accepts it.  Otherwise it selects
         the whole address into `temp`, then shares `Var temp`. -/
      let address := wordInstNormalizeExp address
      match address with
      | .op .add [base, .const offset] =>
          if wordInstSelectShareOffsetAllowed operator offset then
            let (prelude, selectedBase) := wordInstSelectAtom temp base
            wordDeadSelectSeq prelude
              (.shareInst operator name (.op .add [selectedBase, .const offset]))
          else
            let (prelude, _) := wordInstSelectAtom temp address
            wordDeadSelectSeq prelude (.shareInst operator name (.var temp))
      | _ =>
          let (prelude, _) := wordInstSelectAtom temp address
          wordDeadSelectSeq prelude (.shareInst operator name (.var temp))
  | .set store value =>
      /- `inst_select c temp (Set store exp)` (`word_instScript.sml:386-388`)
         is `Seq (inst_select_exp c temp temp (flatten_exp (pull_exp exp)))
         (Set store (Var temp))`.  It runs the expression selector
         unconditionally, so even `Set store (Var v)` becomes
         `Move 0 [(temp, v)]; Set store (Var temp)`.

         Flapjack had no `Set` case at all, so the store passed through
         untouched and the copy was never created.  Full SSA then numbered
         every later name four lower than Cake's and the allocator saw one
         fewer move, which permuted the colours: in the guest's
         `process_transaction` Cake emits
         `Inst (Const 137 0w); Move0 [(141,137)]; Set (Temp 0w) (Var 141)`
         where Flapjack emitted `const 137 0; set (temp 0) (var 137)`. -/
      let (prelude, selected) := wordInstSelectAtom temp (wordInstNormalizeExp value)
      wordDeadSelectSeq prelude (.set store selected)
  | .assign destination value =>
      let value := wordInstNormalizeExp value
      match value with
      | .lookup store => .get destination store
      | .load address =>
          let (prelude, selectedAddress) := wordInstSelectAddressAtom temp address
          match selectedAddress with
          | .var address =>
              wordDeadSelectSeq prelude (.inst (.mem .load destination address))
          | .op .add [.var address, .const offset] =>
              if WordInstSelectImmediate.validSharedMemoryOffset .load offset then
                wordDeadSelectSeq prelude
                  (.inst (.memOffset .load destination address offset))
              else
                let materialize := wordDeadSelectSeq prelude
                  (.inst (.const (temp + 1) offset))
                let materialize := wordDeadSelectSeq materialize
                  (.inst (.arith (.binOp .add temp temp (.reg (temp + 1)))))
                wordDeadSelectSeq materialize
                  (.inst (.mem .load destination temp))
          | _ => wordDeadSelectSeq prelude (.inst (.mem .load destination temp))
      | .op operator [sourceLeft, .const value] =>
          let (prelude, left) := wordInstSelectAtom temp sourceLeft
          match left with
          | .var left =>
              let normal :=
                if WordInstSelectImmediate.validBinOpImmediate operator value then
                  wordDeadSelectSeq prelude
                    (.inst (.arith (.binOp operator destination left (.imm value))))
                else if operator = .add &&
                    WordInstSelectImmediate.validBinOpImmediate .sub
                      (WordInstSelectImmediate.negateImmediate value) then
                  wordDeadSelectSeq prelude
                    (.inst (.arith (.binOp .sub destination left
                      (.imm (WordInstSelectImmediate.negateImmediate value)))))
                else
                  /- Cake's `inst_select_exp` materializes an out-of-range
                     constant in `temp + 1` and emits the register/register
                     instruction.  Leaving this as an expression defers the
                     choice to Word-to-Stack and changes both allocator colours
                     and the emitted RISC-V for wide masks. -/
                  wordDeadSelectSeq prelude
                    (wordDeadSelectSeq (.inst (.const (temp + 1) value))
                      (.inst (.arith (.binOp operator destination left
                        (.reg (temp + 1))))))
              match sourceLeft with
              | .lookup .currHeap =>
                  if operator = .sub then
                    normal
                  else
                    wordDeadSelectSeq (.inst (.const temp value))
                      (.opCurrHeap operator destination temp)
              | _ => normal
          | _ => wordDeadSelectSeq prelude
              (wordDeadSelectSeq
                (.inst (.const (temp + 1) value))
                (.inst (.arith (.binOp operator destination temp
                  (.reg (temp + 1))))))
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
      | .op operator [sourceLeft, sourceRight] =>
          let (leftPrelude, left) := wordInstSelectAtom temp sourceLeft
          let (rightPrelude, right) := wordInstSelectAtom (temp + 1) sourceRight
          let (rightHeapPrelude, _) := wordInstSelectAtom temp sourceRight
          let currentHeapCode : Option (WordProg α) :=
            match sourceLeft, sourceRight with
            | _, .lookup .currHeap =>
                some (wordDeadSelectSeq leftPrelude
                  (.opCurrHeap operator destination temp))
            | .lookup .currHeap, _ =>
                if operator = .sub then
                  none
                else
                  some (wordDeadSelectSeq rightHeapPrelude
                    (.opCurrHeap operator destination temp))
            | _, _ => none
          match currentHeapCode with
          | some code => code
          | none =>
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
      let (prelude, selectedAddress) :=
        wordInstSelectAddressAtom temp (wordInstNormalizeExp address)
      match selectedAddress with
      | .var address =>
          /- Keep the source-shaped Store carrier until Word-to-Stack.  This
             is the carrier that the parity-green compiler used: for ordinary
             addresses the later lowering emits the same sequence as Cake's
             selected Mem instruction, while preserving the allocator-visible
             move shape. -/
          wordDeadSelectSeq prelude (.inst (.mem .store value address))
      | .op .add [.var address, .const offset] =>
          if WordInstSelectImmediate.negativeAddressOffset offset then
            wordDeadSelectSeq prelude
              (.inst (.memOffset .store value address offset))
          else
            wordDeadSelectSeq prelude (.store selectedAddress value)
      | _ => wordDeadSelectSeq prelude (.store selectedAddress value)
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

def wordInstSelectProgramFrom [Sub α] [Add α] [AndOp α] [OrOp α] [HXor α α α]
    [DecidableEq α] [OfNat α 0] [OfNat α 1]
    [WordInstSelectImmediate α] [WordInstSelectConstants α]
    (program : WordProg α) : WordProg α :=
  wordInstSelectProgram (wordInstSelectMaximum (wordProgVariables program) + 1) program

end Flapjack.RiscV
