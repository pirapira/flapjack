import Flapjack.RiscV.WordInstSelect
import Flapjack.Pancake.WordLang

/-!
# Cake's `word_simp$const_fp` program-level constant propagation

`word_simp$compile_exp` runs `Seq_assoc`, `const_fp`, `simp_duplicate_if` and
`push_out_if` before `word_inst$inst_select` (`word_simpScript.sml:491-498`).
Flapjack ports the sequence flattening (`Seq_assoc_right`), the condition
duplication (`wordFuseConditions`) and the expression normalisation inside
`inst_select`, but not `const_fp`.

`const_fp` matters for byte parity because its `Call`, `FFI`, `Alloc` and
`Install` rules re-materialise the argument constants in front of the
operation through `drop_consts`, and `drop_consts` recursively emits the
assignments *outside-in*, i.e. in REVERSED argument order:

  `drop_consts cs (n :: ns) = SmartSeq (drop_consts cs ns) (Assign n (Const w))`

For `g(5, 7)` Cake therefore emits `2 := 7; 6 := 5` just before the call.  The
SSA pass and `remove_dead_prog` then delete the earlier constant
assignments, so the surviving pair is in the reversed order that the
eventual RISC-V `ori` instructions show.  Without the pass Flapjack keeps the
source order (`6 := 5; 2 := 7`), which is the remaining `callee_abi`
mismatch.
-/

namespace Flapjack.RiscV

open Flapjack

/-! `SmartSeq` (`word_simpScript.sml:14-17`): dropping a `Skip` keeps the
    program shape flat, which matters because the following passes look at
    the first constructor of a sequence. -/
def wordSimpSmartSeq (first second : WordProg α) : WordProg α :=
  match first with
  | .skip => second
  | _ => .seq first second

/-! Cake's `Seq_assoc` (`word_simpScript.sml:21-38`) reassociates the
    sequence spine to the left before the other simplifications inspect it.
    The source lowering constructs right-associated sequences, so retaining
    that shape prevents `simp_duplicate_if` from finding the same
    prefix/continuation pair as Cake. -/
def wordSimpSeqItems : WordProg α → List (WordProg α)
  | .seq first second => wordSimpSeqItems first ++ wordSimpSeqItems second
  | program => [program]

def wordSimpLeftSeq : List (WordProg α) → WordProg α
  | [] => .skip
  | statement :: statements =>
      statements.foldl wordSimpSmartSeq statement

/-- `wordSimpSeqItems (wordSimpLeftSeq statements)`, without building the
    intermediate spine.  `wordSimpLeftSeq` folds `wordSimpSmartSeq` from the
    head, and `wordSimpSmartSeq .skip second = second`, so every leading
    `Skip` is dropped while later ones are retained; an all-`Skip` list
    collapses to the single `Skip` that `wordSimpLeftSeq []` returns. -/
def wordSimpLeftSeqItems : List (WordProg α) → List (WordProg α)
  | [] => [.skip]
  | .skip :: statements => wordSimpLeftSeqItems statements
  | statements => statements

/-! Cake's `Seq_assoc` threads the left prefix through an accumulator
    (`word_simpScript.sml:21-38`), so it visits each node once.  Recursing
    into both halves and then re-running `wordSimpSeqItems` over the two
    *already reassociated* results walks the processed spine again at every
    `Seq` node, which is quadratic in the length of the sequence: on the
    stateless guest one 14 325-node function spent 16.4 s here.

    Returning the spine items directly removes the re-walk.  The result is
    unchanged: `wordSimpSeqAssoc` is `wordSimpLeftSeq` of these items, and
    for a `Seq` the previous code took `wordSimpLeftSeq` of the same list
    before `wordSimpLeftSeqItems` dropped its leading `Skip`s -- which
    `wordSimpLeftSeq` drops again on its own.  Cake applies the same
    reassociation under `Call` return and exception-handler metadata, so the
    fuel-driven traversal below descends into those programs too. -/
def wordSimpProgFuel : WordProg α → Nat
  | .seq first second => 1 + wordSimpProgFuel first + wordSimpProgFuel second
  | .ite _ _ _ thenBranch elseBranch =>
      1 + wordSimpProgFuel thenBranch + wordSimpProgFuel elseBranch
  | .loop _ body _ => 1 + wordSimpProgFuel body
  | .mustTerminate body => 1 + wordSimpProgFuel body
  | .call returns _ _ handler =>
      1 + (match returns with
           | some (_, _, returnProgram, _, _) => wordSimpProgFuel returnProgram
           | none => 0)
        + (match handler with
           | some (_, handlerProgram, _, _) => wordSimpProgFuel handlerProgram
           | none => 0)
  | _ => 1

def wordSimpSeqAssocItemsFuel : Nat → WordProg α → List (WordProg α)
  | 0, program => [program]
  | fuel + 1, .seq first second =>
      wordSimpLeftSeqItems
        (wordSimpSeqAssocItemsFuel fuel first ++
          wordSimpSeqAssocItemsFuel fuel second)
  | fuel + 1, .ite operator condition right thenBranch elseBranch =>
      [.ite operator condition right
        (wordSimpLeftSeq (wordSimpSeqAssocItemsFuel fuel thenBranch))
        (wordSimpLeftSeq (wordSimpSeqAssocItemsFuel fuel elseBranch))]
  | fuel + 1, .call returns target arguments handler =>
      let returns := returns.map (fun metadata =>
        let (names, cutsets, returnProgram, firstLabel, secondLabel) := metadata
        (names, cutsets,
          wordSimpLeftSeq (wordSimpSeqAssocItemsFuel fuel returnProgram),
          firstLabel, secondLabel))
      let handler := handler.map (fun metadata =>
        let (exception, handlerProgram, firstLabel, secondLabel) := metadata
        (exception,
          wordSimpLeftSeq (wordSimpSeqAssocItemsFuel fuel handlerProgram),
          firstLabel, secondLabel))
      [.call returns target arguments handler]
  | fuel + 1, .loop liveIn body liveOut =>
      [.loop liveIn (wordSimpLeftSeq (wordSimpSeqAssocItemsFuel fuel body)) liveOut]
  | fuel + 1, .mustTerminate body =>
      [.mustTerminate (wordSimpLeftSeq (wordSimpSeqAssocItemsFuel fuel body))]
  | _, program => [program]
termination_by fuel _ => fuel

def wordSimpSeqAssocItems (program : WordProg α) : List (WordProg α) :=
  wordSimpSeqAssocItemsFuel (wordSimpProgFuel program + 1) program

def wordSimpSeqAssoc (program : WordProg α) : WordProg α :=
  wordSimpLeftSeq (wordSimpSeqAssocItems program)


/-! `strip_const` (`word_simpScript.sml:131-138`). -/
def wordSimpStripConst : List (WordExp α) → Option (List α)
  | [] => some []
  | .const value :: expressions =>
      (wordSimpStripConst expressions).map (fun values => value :: values)
  | _ :: _ => none

/-! Word instruction selection uses the shared `wordLang$word_op` definition. -/
def wordSimpFoldOp [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [Complement α] [OfNat α 0] (operator : BinOp) (values : List α) : Option α :=
  wordOpHOL operator values

class WordSimpShift (α : Type u) where
  eval : Shift → α → α → Option α

instance (priority := 10) defaultWordSimpShift : WordSimpShift α where
  eval _ _ _ := none

instance (priority := 100) bitVecWordSimpShift [NeZero width] :
    WordSimpShift (BitVec width) where
  eval operator left right :=
    if right.toNat < width then
      match operator with
      | .lsl => some (left <<< right.toNat)
      | .lsr => some (left >>> right.toNat)
      | .asr => some (BitVec.sshiftRight left right.toNat)
      | .ror => some (BitVec.rotateRight left right.toNat)
    else none

/-! `const_fp_exp` (`word_simpScript.sml:140-215`). -/
def wordSimpConstExp [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [Complement α] [OfNat α 0] [WordSimpShift α]
    (constants : NatInfoMap α) : WordExp α → WordExp α
  | .var name =>
      match lookupNatInfo name constants with
      | some value => .const value
      | none => .var name
  | .op operator arguments =>
      let folded := arguments.map (wordSimpConstExp constants)
      match wordSimpStripConst folded with
      | some values =>
          match wordSimpFoldOp operator values with
          | some value => .const value
          | none => .op operator (values.map (fun value => .const value))
      | none => .op operator folded
  | .shift operator left right =>
      let left := wordSimpConstExp constants left
      let right := wordSimpConstExp constants right
      match left, right with
      | .const left, .const right =>
          match WordSimpShift.eval operator left right with
          | some value => .const value
          | none => .shift operator (.const left) (.const right)
      | _, _ => .shift operator left right
  /- Cake's `const_fp_exp` has no `Load` clause (`word_simpScript.sml:191-212`),
     so an expression-level load is opaque to constant propagation.  The
     address is selected later, after this pass; descending here changes both
     the live constant assignment and the emitted register allocation. -/
  | .load address => .load address
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

/-! `insert`/`delete` on the port's `NatInfoMap`. -/
def wordSimpMapInsert (constants : NatInfoMap α) (name : Nat) (value : α) : NatInfoMap α :=
  (name, value) :: (constants.filter (fun entry => entry.1 != name))

def wordSimpMapDelete (constants : NatInfoMap α) (name : Nat) : NatInfoMap α :=
  constants.filter (fun entry => entry.1 != name)

def wordSimpMapDeleteAll (constants : NatInfoMap α) (names : List Nat) : NatInfoMap α :=
  names.foldl wordSimpMapDelete constants

/-! `filter_v`/`inter`/`inter_eq` on the constant map.  `is_gc_const`
    (`word_simpScript.sml:255-256`) keeps the constants whose low bit is
    clear, which is exactly the pair-tagged-word test. -/
def wordSimpMapFilterGc [AndOp α] [OfNat α 1] [OfNat α 0] [DecidableEq α]
    (constants : NatInfoMap α) : NatInfoMap α :=
  constants.filter (fun entry => decide ((entry.2 &&& (1 : α)) = 0))

def wordSimpMapInter (constants : NatInfoMap α) (names : List Nat) : NatInfoMap α :=
  constants.filter (fun entry => names.contains entry.1)

def wordSimpMapInterEq [DecidableEq α] (first second : NatInfoMap α) : NatInfoMap α :=
  first.filter (fun entry => lookupNatInfo entry.1 second == some entry.2)

/-! `const_fp_move_cs` (`word_simpScript.sml:217-227`). -/
def wordSimpMoveConstants [DecidableEq α] (moves : List (Nat × Nat))
    (original : NatInfoMap α) (constants : NatInfoMap α) : NatInfoMap α :=
  moves.foldl (fun current move =>
    match lookupNatInfo move.2 original with
    | some value => wordSimpMapInsert current move.1 value
    | none => wordSimpMapDelete current move.1) constants

/-! `const_fp_inst_cs` (`word_simpScript.sml:229-249`). -/
def wordSimpInstConstants {α : Type} (constants : NatInfoMap α) :
    WordInst α → NatInfoMap α
  | .arith (.binOp _ destination _ _) => wordSimpMapDelete constants destination
  | .arith (.addCarry destination _ _ _ carryIn) =>
      wordSimpMapDelete (wordSimpMapDelete constants carryIn) destination
  | .arith (.cakeAddCarry destination _ _ carry) =>
      wordSimpMapDelete (wordSimpMapDelete constants carry) destination
  | .arith (.longMul destinationLeft destinationRight _ _) =>
      wordSimpMapDelete (wordSimpMapDelete constants destinationLeft) destinationRight
  | .arith (.longDiv destinationLeft destinationRight _ _ _) =>
      wordSimpMapDelete (wordSimpMapDelete constants destinationLeft) destinationRight
  | .arith (.div destination _ _) => wordSimpMapDelete constants destination
  | .arith (.shift _ destination _ _) =>
      wordSimpMapDelete constants destination
  | .const destination _ => wordSimpMapDelete constants destination
  | .mem _ destination _ => wordSimpMapDelete constants destination
  | .memOffset _ destination _ _ => wordSimpMapDelete constants destination

/-! `get_var_imm_cs` (`word_simpScript.sml:251-253`). -/
def wordSimpGetVarImm [DecidableEq α] (constants : NatInfoMap α) :
    WordRegImm α → Option α
  | .reg name => lookupNatInfo name constants
  | .imm value => some value

/-! `asm$word_cmp` as used by `word_simp$const_fp`.  Comparisons in the Word
    program are target-word comparisons: `Lower` is unsigned, `Less` is
    signed, and `Test` checks whether the bitwise conjunction is zero. -/
def wordSimpEvalCmp [BEq α] [OfNat α 0] [AndOp α] [PanCmp α]
    (operator : Cmp) (left right : α) : Bool :=
  match operator with
  | .equal => left == right
  | .notEqual => !(left == right)
  | .lower => PanCmp.lower left right
  | .less => PanCmp.less left right
  | .notLower => !(PanCmp.lower left right)
  | .notLess => !(PanCmp.less left right)
  | .test => AndOp.and left right == 0
  | .notTest => !(AndOp.and left right == 0)

/-! `drop_consts` (`word_simpScript.sml:270-275`).  The recursion puts the
    remaining arguments before the current assignment, which reverses the
    order relative to the argument list. -/
def wordSimpDropConsts (constants : NatInfoMap α) : List Nat → WordProg α
  | [] => .skip
  | name :: names =>
      match lookupNatInfo name constants with
      | none => wordSimpDropConsts constants names
      | some value =>
          wordSimpSmartSeq (wordSimpDropConsts constants names) (.assign name (.const value))

/-! `const_fp_loop` (`word_simpScript.sml:277-339`).  When both sides of an
    `If` comparison are known constants, Cake evaluates the comparison and
    continues with the selected branch.  This branch-sensitive propagation is
    important: after an outer comparison assigns a 0/1 result, nested tests of
    that result are folded away. -/
def wordConstFpLoop [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [Complement α] [OfNat α 1] [OfNat α 0] [DecidableEq α] [PanCmp α]
    [WordSimpShift α] :
    WordProg α → NatInfoMap α → WordProg α × NatInfoMap α
  | .skip, constants => (.skip, constants)
  | .move priority moves, constants =>
      (.move priority moves, wordSimpMoveConstants moves constants constants)
  | .assign name value, constants =>
      let value := wordSimpConstExp constants value
      match value with
      | .const constant => (.assign name value, wordSimpMapInsert constants name constant)
      | _ => (.assign name value, wordSimpMapDelete constants name)
  | .inst instruction, constants =>
      (.inst instruction, wordSimpInstConstants constants instruction)
  | .get destination store, constants =>
      (.get destination store, wordSimpMapDelete constants destination)
  | .opCurrHeap operator destination source, constants =>
      (.opCurrHeap operator destination source, wordSimpMapDelete constants destination)
  | .mustTerminate body, constants =>
      let (body, constants') := wordConstFpLoop body constants
      (.mustTerminate body, constants')
  | .seq first second, constants =>
      let (first, constants') := wordConstFpLoop first constants
      let (second, constants'') := wordConstFpLoop second constants'
      (.seq first second, constants'')
  | .ite operator condition right thenBranch elseBranch, constants =>
      match lookupNatInfo condition constants, wordSimpGetVarImm constants right with
      | some leftValue, some rightValue =>
          if wordSimpEvalCmp operator leftValue rightValue then
            wordConstFpLoop thenBranch constants
          else
            wordConstFpLoop elseBranch constants
      | _, _ =>
          let (thenBranch, thenConstants) := wordConstFpLoop thenBranch constants
          let (elseBranch, elseConstants) := wordConstFpLoop elseBranch constants
          (.ite operator condition right thenBranch elseBranch,
            wordSimpMapInterEq thenConstants elseConstants)
  | .loop liveIn body liveOut, _ =>
      let (body, _) := wordConstFpLoop body []
      (.loop liveIn body liveOut, [])
  | .call returns target arguments handler, constants =>
      let dropped := wordSimpDropConsts constants arguments
      match returns with
      | none =>
          (wordSimpSmartSeq dropped (.call none target arguments handler),
            wordSimpMapFilterGc constants)
      | some (names, cutsets, returnProgram, firstLabel, secondLabel) =>
          match handler with
          | some _ =>
              (wordSimpSmartSeq dropped
                (.call (some (names, cutsets, returnProgram, firstLabel, secondLabel))
                  target arguments handler), [])
          | none =>
              let restrict := wordSimpMapDeleteAll
                (wordSimpMapFilterGc (wordSimpMapInter constants (cutsets.1 ++ cutsets.2)))
                names
              let (returnProgram, constants') := wordConstFpLoop returnProgram restrict
              (wordSimpSmartSeq dropped
                (.call (some (names, cutsets, returnProgram, firstLabel, secondLabel))
                  target arguments handler), constants')
  | .alloc destination cutsets, constants =>
      (wordSimpSmartSeq (wordSimpDropConsts constants [destination])
          (.alloc destination cutsets),
        wordSimpMapFilterGc (wordSimpMapInter constants (cutsets.1 ++ cutsets.2)))
  | .storeConsts source bitmap codeLength dataLength constantsList, constants =>
      (.storeConsts source bitmap codeLength dataLength constantsList,
        wordSimpMapDeleteAll constants [source, bitmap, codeLength, dataLength])
  | .install codeBuffer codeLength dataBuffer dataLength cutsets, constants =>
      (wordSimpSmartSeq (wordSimpDropConsts constants
          [codeBuffer, codeLength, dataBuffer, dataLength])
          (.install codeBuffer codeLength dataBuffer dataLength cutsets),
        wordSimpMapDelete
          (wordSimpMapFilterGc (wordSimpMapInter constants (cutsets.1 ++ cutsets.2)))
          codeBuffer)
  | .ffi function configuration configurationLength array arrayLength live, constants =>
      (wordSimpSmartSeq (wordSimpDropConsts constants
          [configuration, configurationLength, array, arrayLength])
          (.ffi function configuration configurationLength array arrayLength live),
        wordSimpMapInter constants (live.1 ++ live.2))
  | .locValue destination source, constants =>
      (.locValue destination source, wordSimpMapDelete constants destination)
  | .store address value, constants =>
      (.store (wordSimpConstExp constants address) value, constants)
  | .shareInst operator name address, constants =>
      let address := wordSimpConstExp constants address
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          (.shareInst operator name address, wordSimpMapDelete constants name)
      | _ => (.shareInst operator name address, constants)
  | program, constants => (program, constants)
termination_by program _ => sizeOf program
decreasing_by all_goals decreasing_trivial

/-- `const_fp` (`word_simpScript.sml:342-344`). -/
def wordConstFp [Add α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [Complement α] [OfNat α 1] [OfNat α 0] [DecidableEq α] [PanCmp α]
    [WordSimpShift α]
    (program : WordProg α) : WordProg α :=
  (wordConstFpLoop (wordSimpSeqAssoc program) []).1

end Flapjack.RiscV
