import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Word
import Flapjack.Compiler.Backend.WordCse.InstructionKeys
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
import Std.Data.TreeMap

/-!
# Cake's Word common-subexpression elimination

This is a port of `word_cseScript.sml`, the pass that CakeML runs as
`word_common_subexp_elim` immediately after the full-SSA pass and its
dead-program elimination.  Cake's pass is a knowledge-based CSE: it keeps a
table of the selected instructions it has already seen and rewrites a later
occurrence as a move of the earlier result.  The table is keyed by a numeral
hash of the instruction (`instToNumList`), and the register maps record which
register currently holds which equivalent value (`to_canonical`/`to_latest`),
so a repeated `Get HeapLength`, shift, or heap address is shared across the
whole function.  Without it a duplicate global initializer recomputes its
address and diverges from Cake by several bytes.

The port keeps Cake's structure; its only deviations are about the carrier:

* generic diagnostic values use `WordCseHash`; executed positive-width
  machine words delegate reviewed native `wordToNum` and `regImmToNumList`
  through a constructor-for-constructor immediate codec; shared arithmetic
  keys also execute native `arithToNumList` through the positional codec,
  and load-offset keys execute native `loadToNumList`;
* the two `num_map`s, the `store_name` alist and the two balanced maps are
  represented by association lists (`lookupNatInfo` is Cake's `lookup_any`,
  a first-match lookup, and `wordCseInsert` is a replacement insert);
* the fact tables pass the reviewed native `listCmp` directly to TreeMap;
  this comparator agrees unconditionally with the previous Lean list ordering;
* `WordMemOp` has no immediate address offset, so the address offset in
  `loadToNumList` is always `0`;
* Cake's `fpWrites`/FP rows and the `AddOverflow`/`SubOverflow` carriers do
  not exist in the port, and the port's five-register `.addCarry` has no
  Cake counterpart, so it is never CSE'd (Cake's `can_mem_arith` catch-all is
  `F` as well).
-/

namespace Flapjack.RiscV

open Flapjack

/-- Cake's `wordToNum`: the numeral carried by a machine word. -/
class WordCseHash (α : Type u) where
  hash : α → Nat
  nativeArithKey : WordArith α → Option (List Nat) := fun _ => none
  nativeInstKey : WordInst α → Option (List Nat) := fun _ => none
  nativeArithInfo : WordArith α → Option (Nat × List Nat × List Nat × Bool) := fun _ => none
  loadKey : WordMemOp → Nat → α → List Nat := fun operator address offset =>
    [Compiler.Backend.WordCse.memOpToNum operator, address + 100, hash offset]
  regImmKey : WordRegImm α → List Nat := fun
    | .reg register => [33, register + 100]
    | .imm value => [34, hash value]

instance (priority := low) {width : Nat} : WordCseHash (BitVec width) where
  hash value := value.toNat

/-- Constructor codec for the executed positive-width word immediate carrier.
Flapjack infrastructure: the source and target constructors carry the same word. -/
def wordCseNativeRegImm {width : Nat} [NeZero width] :
    WordRegImm (BitVec width) → Flapjack.Compiler.Encoders.Asm.HolRegImm width
  | .reg register => .reg register
  | .imm value => .imm value

/-- Production instruction embedding for keys. Offset-free memory explicitly
means native Addr base zero; other shared constructors use the existing codec.
The separate five-register AddCarry is rejected. Flapjack routing infrastructure,
not a HOL datatype port or an instruction simulation theorem. -/
def wordCseNativeInst? {width : Nat} [NeZero width] :
    WordInst (BitVec width) → Option (Compiler.Encoders.Asm.HolInst width)
  | .mem operator destination base => some (.mem operator destination (.addr base 0))
  | instruction => Compiler.Backend.StackToLab.ExecutedCodec.instFromExecuted? (.word instruction)

/-- Machine-word CSE executes the reviewed native encoders. The lower-priority
zero-width/generic diagnostic instance remains outside the HOL word claim. -/
instance {width : Nat} [NeZero width] : WordCseHash (BitVec width) where
  hash := Flapjack.Compiler.Backend.WordCse.wordToNum
  nativeArithInfo operation :=
    (Compiler.Backend.StackToLab.ExecutedCodec.arithFromExecuted? operation).map
      (fun native => (Compiler.Backend.WordCse.firstRegOfArith native,
        Compiler.Backend.WordCse.arithWrites native,
        Compiler.Backend.WordCse.arithReads native,
        Compiler.Backend.WordCse.canMemArith native))
  loadKey := Compiler.Backend.WordCse.loadToNumList
  nativeInstKey instruction := (wordCseNativeInst? instruction).map
    Compiler.Backend.WordCse.instToNumList
  nativeArithKey operation :=
    (Compiler.Backend.StackToLab.ExecutedCodec.arithFromExecuted? operation).map
      Compiler.Backend.WordCse.arithToNumList
  regImmKey immediate := Flapjack.Compiler.Backend.WordCse.regImmToNumList
    (wordCseNativeRegImm immediate)

/-- The executable Word-to-Word probes also run on plain numerals, where the
    numeral is its own hash. -/
instance : WordCseHash Nat where
  hash value := value

/-- Cake's `store_name` occurrences are keyed by a numeral, mirroring the
    hashing of instructions.  Only equality and disequality of the keys are
    observable, plus the `CurrHeap` test in Cake's `Set` rule. -/
def wordCseStoreCode [WordCseHash α] : WordStore α → Nat
  | .nextFree => 1
  | .endOfHeap => 2
  | .triggerGC => 3
  | .heapLength => 4
  | .progStart => 5
  | .bitmapBase => 6
  | .currHeap => 7
  | .otherHeap => 8
  | .allocSize => 9
  | .globals => 10
  | .globReal => 11
  | .handler => 12
  | .genStart => 13
  | .codeBuffer => 14
  | .codeBufferEnd => 15
  | .bitmapBuffer => 16
  | .bitmapBufferEnd => 17
  | .temp address => 1000 + WordCseHash.hash address

def wordCseIsCurrHeap : WordStore α → Bool
  | .currHeap => true
  | _ => false

/-! Cake's `knowledge` keeps `to_canonical`, `to_latest` and `gets_mem` in
`num_map`s and `instrs_mem`/`loads_mem` in balanced maps keyed by numeral
lists (`word_cseScript.sml`), so every insert and lookup is logarithmic.
Holding them as association lists made each insert rebuild the whole list and
each lookup scan it, and `word_common_subexp_elim` was the largest
non-allocator cost on the real guest: 1785 ms of a 1930 ms preprocess chain
on its biggest function.

Every key in these maps is unique -- the list form removed the old binding
before consing the new one -- and they are only ever read back by key, so
replacing the lists with trees changes no value the pass computes.  The
whole-program byte comparison in the commit message is the evidence. -/
abbrev WordCseRegMap := Std.TreeMap Nat Nat
abbrev WordCseFactMap :=
  Std.TreeMap (List Nat) Nat Compiler.Backend.WordCse.listCmp

/-- Cake's `knowledge` record.  `toCanonical` and `toLatest` are the two
    register maps, `getsMem` records the register that already holds a store
    value, and `instrsMem`/`loadsMem` are the instruction and load fact
    tables.  Every key is a numeral hash, so the knowledge carries no word
    values. -/
structure WordCseKnowledge where
  toCanonical : WordCseRegMap
  toLatest : WordCseRegMap
  getsMem : WordCseRegMap
  instrsMem : WordCseFactMap
  loadsMem : WordCseFactMap

def wordCseEmpty : WordCseKnowledge :=
  { toCanonical := ∅, toLatest := ∅, getsMem := ∅, instrsMem := ∅, loadsMem := ∅ }

/-- Replacement insert, Cake's `num_map` `insert`. -/
def wordCseInsert (key value : Nat) (map : WordCseRegMap) : WordCseRegMap :=
  map.insert key value

/-- Replacement insert for the balanced-map keys, which are numeral lists. -/
def wordCseListInsert (key : List Nat) (value : Nat)
    (map : WordCseFactMap) : WordCseFactMap :=
  map.insert key value

def wordCseListLookup (key : List Nat) (map : WordCseFactMap) : Option Nat :=
  map[key]?

/-- Cake's `lookup_any`: a lookup with a default for missing keys. -/
def wordCseLookupAny (key : Nat) (map : WordCseRegMap) (default : Nat) : Nat :=
  (map[key]?).getD default

/-- Cake's `map_insert` folds `insert` over the entries so the head of the
    list is inserted last and therefore wins. -/
def wordCseMapInsert (entries : List (Nat × Nat)) (map : WordCseRegMap) :
    WordCseRegMap :=
  entries.foldr (fun entry accumulated => wordCseInsert entry.1 entry.2 accumulated) map

/-- Cake's `keep_data canon write_to_reg = IS_NONE (lookup write_to_reg canon)`. -/
def wordCseKeepData (data : WordCseKnowledge) (written : Nat) : Bool :=
  (data.toCanonical[written]?).isNone

/-- Cake's `invalidate_data`: writing a tracked register discards everything. -/
def wordCseInvalidate (data : WordCseKnowledge) (written : Nat) : WordCseKnowledge :=
  if wordCseKeepData data written then data else wordCseEmpty

def wordCseInvalidateRegs (data : WordCseKnowledge) (written : List Nat) :
    WordCseKnowledge :=
  /- `invalidate_data` is absorbing: once one written register is tracked,
     the knowledge becomes empty and every later invalidation is a no-op.
     Cake's fold is therefore equivalent to this single membership scan, but
     the scan avoids rebuilding the five maps for every register in a write
     set (notably the four-register StoreConsts boundary). -/
  if written.any (fun register => (data.toCanonical[register]?).isSome) then
    wordCseEmpty
  else data

/-- Cake's `register_read`: an odd register a stored fact reads is entered as
    a self-mapping, so a later write to it resets the data. -/
def wordCseRegisterRead (data : WordCseKnowledge) (register : Nat) : WordCseKnowledge :=
  if register % 2 != 0 && wordCseKeepData data register then
    { data with toCanonical := wordCseInsert register register data.toCanonical }
  else data

def wordCseRegisterReads (data : WordCseKnowledge) (registers : List Nat) :
    WordCseKnowledge :=
  registers.foldl (fun accumulated register => wordCseRegisterRead accumulated register) data

def wordCseCanonicalRegs (data : WordCseKnowledge) (register : Nat) : Nat :=
  wordCseLookupAny register data.toCanonical register

def wordCseCanonicalRegs' (avoid : Nat) (data : WordCseKnowledge) (register : Nat) : Nat :=
  let canonical := wordCseCanonicalRegs data register
  if canonical = avoid then register else canonical

def wordCseCanonicalImmReg (data : WordCseKnowledge) : WordRegImm α → WordRegImm α
  | .reg register => .reg (wordCseCanonicalRegs data register)
  | .imm value => .imm value

def wordCseCanonicalImmReg' (avoid : Nat) (data : WordCseKnowledge) :
    WordRegImm α → WordRegImm α
  | .reg register => .reg (wordCseCanonicalRegs' avoid data register)
  | .imm value => .imm value

/-- Cake's `canonicalMoveRegs`.  The sources are registered first so a
    register that is both a source and a destination fails the `keep_data`
    check and no equivalence is recorded across a self-interfering parallel
    move. -/
def wordCseCanonicalMoveRegs (data : WordCseKnowledge) (moves : List (Nat × Nat)) :
    WordCseKnowledge :=
  let data := wordCseRegisterReads data (moves.map (fun move => move.2))
  if moves.all (fun move => wordCseKeepData data move.1) then
    let tracked := moves.filter (fun move => move.1 % 2 != 0 && move.2 % 2 != 0)
    let canonical := tracked.map (fun move => (move.1, wordCseCanonicalRegs data move.2))
    let inverted := canonical.map (fun move => (move.2, move.1))
    { data with
        toCanonical := wordCseMapInsert canonical data.toCanonical,
        toLatest := wordCseMapInsert inverted data.toLatest }
  else wordCseEmpty

def wordCseCanonicalArith (data : WordCseKnowledge) : WordArith α → WordArith α
  | .binOp operator destination sourceLeft sourceRight =>
      .binOp operator destination (wordCseCanonicalRegs' destination data sourceLeft)
        (wordCseCanonicalImmReg' destination data sourceRight)
  | .shift operator destination sourceLeft sourceRight =>
      .shift operator destination (wordCseCanonicalRegs' destination data sourceLeft)
        (wordCseCanonicalImmReg' destination data sourceRight)
  | .div destination dividend divisor =>
      .div destination (wordCseCanonicalRegs data dividend)
        (wordCseCanonicalRegs data divisor)
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      .longMul destinationLeft destinationRight (wordCseCanonicalRegs data sourceLeft)
        (wordCseCanonicalRegs data sourceRight)
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      .longDiv destinationLeft destinationRight (wordCseCanonicalRegs data sourceLeft)
        (wordCseCanonicalRegs data sourceRight) (wordCseCanonicalRegs data quotient)
  | .cakeAddCarry destination sourceLeft sourceRight carry =>
      .cakeAddCarry destination (wordCseCanonicalRegs' destination data sourceLeft)
        (wordCseCanonicalRegs' destination data sourceRight) carry
  | .addOverflow d l r flag =>
      .addOverflow d (wordCseCanonicalRegs' d data l)
        (wordCseCanonicalRegs' d data r) flag
  | .subOverflow d l r flag =>
      .subOverflow d (wordCseCanonicalRegs' d data l)
        (wordCseCanonicalRegs' d data r) flag
  /- The five-register two-result primitive has no Cake counterpart and is
     never recorded, so its operands are left alone. -/
  | operation => operation

/-- Executed CSE delegates the reviewed native scalar encoder; the carrier is identical. -/
def wordCseShiftToNum (operator : Shift) : Nat :=
  Flapjack.Compiler.Backend.WordCse.shiftToNum operator

/-- Executed CSE delegates the reviewed native scalar encoder; the carrier is identical. -/
def wordCseBinOpToNum (operator : BinOp) : Nat :=
  Flapjack.Compiler.Backend.WordCse.arithOpToNum operator

def wordCseRegImmToNumList [WordCseHash α] (immediate : WordRegImm α) : List Nat :=
  WordCseHash.regImmKey immediate

private def wordCseArithDiagnosticKey [WordCseHash α] : WordArith α → List Nat
  | .binOp operator _ sourceLeft sourceRight =>
      [25, wordCseBinOpToNum operator, sourceLeft + 100] ++
        wordCseRegImmToNumList sourceRight
  | .shift operator _ sourceLeft sourceRight =>
      [28, wordCseShiftToNum operator, sourceLeft + 100] ++
        wordCseRegImmToNumList sourceRight
  | .longMul _ _ sourceLeft sourceRight => [26, sourceLeft + 100, sourceRight + 100]
  | .longDiv _ _ sourceLeft sourceRight quotient =>
      [27, sourceLeft + 100, sourceRight + 100, quotient + 100]
  | .div _ dividend divisor => [29, dividend + 100, divisor + 100]
  | .cakeAddCarry _ sourceLeft sourceRight _ => [30, sourceLeft + 100, sourceRight + 100]
  | .addOverflow _ l r _ => [31, l + 100, r + 100]
  | .subOverflow _ l r _ => [32, l + 100, r + 100]
  /- Never stored, so the hash only has to be distinct from the stored
     heads; `can_mem_arith` rejects the five-register primitive. -/
  | .addCarry _ _ _ _ _ => [31]

/-- Positive-width executed words use the reviewed native arithmetic encoder
through its existing positional codec. Generic diagnostics and the distinct
five-register AddCarry extension retain their explicit diagnostic key. This
routing infrastructure is not a full arithmetic-carrier or CSE correctness port. -/
def wordCseArithToNumList [WordCseHash α] (operation : WordArith α) : List Nat :=
  match WordCseHash.nativeArithKey operation with
  | some key => key
  | none => wordCseArithDiagnosticKey operation

/-- Successful canonical arithmetic conversion makes the actual executed key
exactly the native key. Flapjack codec correspondence, with no HOL original;
this assumes only carrier conversion, not a target run or simulation. -/
theorem wordCseArithToNumList_native {width : Nat} [NeZero width]
    (operation : WordArith (BitVec width)) (native : Compiler.Encoders.Asm.HolArith width)
    (converted : Compiler.Backend.StackToLab.ExecutedCodec.arithFromExecuted? operation = some native) :
    wordCseArithToNumList operation = Compiler.Backend.WordCse.arithToNumList native := by
  simp [wordCseArithToNumList, WordCseHash.nativeArithKey, converted]

/-- Executed CSE delegates the reviewed native scalar encoder; the carrier is identical. -/
def wordCseMemOpToNum (operator : WordMemOp) : Nat :=
  Flapjack.Compiler.Backend.WordCse.memOpToNum operator

/-- Cake's `loadToNumList`.  `WordInst.mem` has no immediate address offset,
    so the offset component is `0` there. -/
def wordCseLoadToNumList (operator : WordMemOp) (address : Nat) : List Nat :=
  [wordCseMemOpToNum operator, address + 100, 0]

/-- `loadToNumList` for the expression carrier.  Cake's `Addr n2 offset`
    carries the offset into the hash; `WordInst.mem` cannot, so a load with a
    non-zero offset is held as `.assign dest (.load (.op .add [.var n2,
    .const offset]))` until `wordToStack` selects its native address.  Hashing that carrier the
    same way lets `word_cse` see those loads, which is how Cake shares a
    repeated global read.  A zero offset hashes to the same key as the
    instruction form, which is correct: they denote the same load. -/
def wordCseLoadOffsetToNumList [WordCseHash α] (operator : WordMemOp)
    (address : Nat) (offset : α) : List Nat :=
  WordCseHash.loadKey operator address offset

/-- Actual positive-width load keys execute the full native encoder. This
unconditional equality is Flapjack routing infrastructure with no HOL original. -/
theorem wordCseLoadOffsetToNumList_native {width : Nat} [NeZero width]
    (operator : WordMemOp) (address : Nat) (offset : BitVec width) :
    wordCseLoadOffsetToNumList operator address offset =
      Compiler.Backend.WordCse.loadToNumList operator address offset := rfl

/-- Heap-address facts execute the reviewed word-free encoder. -/
def wordCseHeapToNumList (operator : BinOp) (source : Nat) : List Nat :=
  Compiler.Backend.WordCse.opCurrHeapToNumList operator source

/-- Cake's `instToNumList`.  The `Const` hash deliberately omits the
    destination so that two constants with the same value share a key. -/
private def wordCseInstDiagnosticKey [WordCseHash α] : WordInst α → List Nat
  | .const _ value => [2, WordCseHash.hash value]
  | .arith operation => 3 :: wordCseArithToNumList operation
  | .mem _ _ _ => [1]
  | .memOffset _ _ _ _ => [1]

/-- Representable machine-word instructions execute native instToNumList.
Memory uses the original [1] catch-all; actual load facts use the separate load
key helper. Generic diagnostics and the five-register extension stay explicit. -/
def wordCseInstToNumList [WordCseHash α] (instruction : WordInst α) : List Nat :=
  match WordCseHash.nativeInstKey instruction with
  | some key => key
  | none => wordCseInstDiagnosticKey instruction

/-- Exact key correspondence for successful production carrier conversion.
Flapjack infrastructure with no HOL original; no run or simulation is assumed. -/
theorem wordCseInstToNumList_native {width : Nat} [NeZero width]
    (instruction : WordInst (BitVec width)) (native : Compiler.Encoders.Asm.HolInst width)
    (converted : wordCseNativeInst? instruction = some native) :
    wordCseInstToNumList instruction = Compiler.Backend.WordCse.instToNumList native := by
  simp [wordCseInstToNumList, WordCseHash.nativeInstKey, converted]

/-- Actual store detection delegates the reviewed identical memory carrier. -/
def wordCseIsStore (operator : WordMemOp) : Bool :=
  Compiler.Backend.WordCse.isStore operator

private def wordCseFirstRegDiagnostic : WordArith α → Nat
  | .binOp _ destination _ _ => destination
  | .shift _ destination _ _ => destination
  | .div destination _ _ => destination
  | .longMul destinationLeft _ _ _ => destinationLeft
  | .longDiv destinationLeft _ _ _ _ => destinationLeft
  | .addOverflow destination _ _ _
  | .subOverflow destination _ _ _
  | .cakeAddCarry destination _ _ _ => destination
  | .addCarry destination _ _ _ _ => destination

private def wordCseArithWritesDiagnostic : WordArith α → List Nat
  | .binOp _ destination _ _ => [destination]
  | .shift _ destination _ _ => [destination]
  | .div destination _ _ => [destination]
  | .longMul destinationLeft destinationRight _ _ => [destinationLeft, destinationRight]
  | .longDiv destinationLeft destinationRight _ _ _ => [destinationLeft, destinationRight]
  | .addOverflow destination _ _ carry
  | .subOverflow destination _ _ carry
  | .cakeAddCarry destination _ _ carry => [destination, carry]
  | .addCarry destination resultCarry _ _ _ => [destination, resultCarry]

private def wordCseArithReadsDiagnostic : WordArith α → List Nat
  | .binOp _ _ sourceLeft (.reg sourceRight) => [sourceLeft, sourceRight]
  | .binOp _ _ sourceLeft (.imm _) => [sourceLeft]
  | .shift _ _ sourceLeft (.reg sourceRight) => [sourceLeft, sourceRight]
  | .shift _ _ sourceLeft (.imm _) => [sourceLeft]
  | .div _ dividend divisor => [dividend, divisor]
  | .longMul _ _ sourceLeft sourceRight => [sourceLeft, sourceRight]
  | .longDiv _ _ sourceLeft sourceRight quotient => [sourceLeft, sourceRight, quotient]
  | .addOverflow _ l r _ | .subOverflow _ l r _ => [l, r]
  | .cakeAddCarry _ sourceLeft sourceRight carry => [sourceLeft, sourceRight, carry]
  | .addCarry _ _ sourceLeft sourceRight carryIn => [sourceLeft, sourceRight, carryIn]

/-- Cake's `can_mem_arith`: only instructions whose operands are odd
    registers (or an odd register with an immediate) may be shared through
    the fact table. -/
private def wordCseCanMemArithDiagnostic : WordArith α → Bool
  | .binOp _ _ sourceLeft (.reg sourceRight) =>
      sourceLeft % 2 != 0 && sourceRight % 2 != 0
  | .binOp _ _ sourceLeft (.imm _) => sourceLeft % 2 != 0
  | .div _ dividend divisor => dividend % 2 != 0 && divisor % 2 != 0
  | .shift _ _ destination (.imm _) => destination % 2 != 0
  | _ => false

/-- Executed shared arithmetic destination, through reviewed native classifiers.
The fallback is generic diagnostic or Flapjack extension infrastructure. -/
def wordCseFirstRegOfArith [WordCseHash α] (operation : WordArith α) : Nat :=
  match WordCseHash.nativeArithInfo operation with
  | some info => info.1
  | none => wordCseFirstRegDiagnostic operation

/-- Executed shared arithmetic writes, preserving native positional carry output. -/
def wordCseArithWrites [WordCseHash α] (operation : WordArith α) : List Nat :=
  match WordCseHash.nativeArithInfo operation with
  | some info => info.2.1
  | none => wordCseArithWritesDiagnostic operation

/-- Executed shared arithmetic reads, including the native carry input. -/
def wordCseArithReads [WordCseHash α] (operation : WordArith α) : List Nat :=
  match WordCseHash.nativeArithInfo operation with
  | some info => info.2.2.1
  | none => wordCseArithReadsDiagnostic operation

/-- Native sharing eligibility for represented instructions. The separate
five-register extension is excluded even for an arbitrary diagnostic instance,
so CSE cannot erase an unsupported input and hide its codec failure. -/
def wordCseCanMemArith [WordCseHash α] : WordArith α → Bool
  | .addCarry _ _ _ _ _ => false
  | operation => match WordCseHash.nativeArithInfo operation with
    | some info => info.2.2.2
    | none => wordCseCanMemArithDiagnostic operation

/-- Exact four-classifier correspondence on successful positional conversion.
Flapjack routing infrastructure, not a HOL simulation or theorem port. -/
theorem wordCseArithInfo_native {width : Nat} [NeZero width]
    (operation : WordArith (BitVec width)) (native : Compiler.Encoders.Asm.HolArith width)
    (converted : Compiler.Backend.StackToLab.ExecutedCodec.arithFromExecuted? operation = some native) :
    wordCseFirstRegOfArith operation = Compiler.Backend.WordCse.firstRegOfArith native ∧
    wordCseArithWrites operation = Compiler.Backend.WordCse.arithWrites native ∧
    wordCseArithReads operation = Compiler.Backend.WordCse.arithReads native ∧
    wordCseCanMemArith operation = Compiler.Backend.WordCse.canMemArith native := by
  cases operation <;>
    simp [Compiler.Backend.StackToLab.ExecutedCodec.arithFromExecuted?] at converted
  all_goals subst native
  all_goals simp [wordCseFirstRegOfArith, wordCseArithWrites, wordCseArithReads,
    wordCseCanMemArith, WordCseHash.nativeArithInfo,
    Compiler.Backend.StackToLab.ExecutedCodec.arithFromExecuted?]

/-- Cake's `add_to_data_aux`/`add_to_load_aux`, shared by the instruction and
    load fact tables.  `table` is the fact map consulted for a repeated
    instruction and `insert` records the new fact when it is seen first. -/
def wordCseAddToFact (data : WordCseKnowledge) (table : WordCseFactMap)
    (register : Nat) (key : List Nat) (instruction : WordProg α)
    (insert : WordCseKnowledge → Nat → WordCseKnowledge) : WordProg α × WordCseKnowledge :=
  match wordCseListLookup key table with
  | some previous =>
      let latest := wordCseLookupAny previous data.toLatest previous
      if register % 2 == 0 then
        (.move 0 [(register, latest)], data)
      else
        (.move 0 [(register, latest)],
          { data with
              toCanonical := wordCseInsert register previous data.toCanonical
              toLatest := wordCseInsert previous register data.toLatest })
  | none =>
      if register % 2 == 0 then
        (instruction, data)
      else
        let recorded := insert data register
        (instruction,
          { recorded with
              toCanonical := wordCseInsert register register recorded.toCanonical
              toLatest := wordCseInsert register register recorded.toLatest })

def wordCseRecordInst (data : WordCseKnowledge) (register : Nat) (key : List Nat) :
    WordCseKnowledge :=
  { data with instrsMem := wordCseListInsert key register data.instrsMem }

/-- Cake's `add_to_data`: a repeated selected instruction becomes a move from
    the register that already holds the earlier result. -/
def wordCseAddToData [WordCseHash α] (data : WordCseKnowledge) (register : Nat)
    (adjusted : WordArith α) (original : WordArith α) : WordProg α × WordCseKnowledge :=
  wordCseAddToFact data data.instrsMem register (wordCseInstToNumList (.arith adjusted))
    (.inst (.arith original))
    (fun data register => wordCseRecordInst data register (wordCseInstToNumList (.arith adjusted)))

/-- Cake's `add_to_load_aux`. -/
def wordCseAddToLoad (data : WordCseKnowledge) (register : Nat) (key : List Nat)
    (instruction : WordProg α) : WordProg α × WordCseKnowledge :=
  wordCseAddToFact data data.loadsMem register key instruction
    (fun data register => { data with loadsMem := wordCseListInsert key register data.loadsMem })

/-- Cake's `add_to_data_const`: a repeated constant is rematerialised rather
    than replaced by a move, but the register equivalence is still recorded
    so later reads can be canonicalised. -/
def wordCseAddToDataConst [WordCseHash α] (data : WordCseKnowledge) (register : Nat) (value : α) :
    WordProg α × WordCseKnowledge :=
  let key := wordCseInstToNumList (.const register value)
  match wordCseListLookup key data.instrsMem with
  | some previous =>
      (.inst (.const register value),
        { data with
            toCanonical := wordCseInsert register previous data.toCanonical,
            toLatest := wordCseInsert previous register data.toLatest })
  | none =>
      (.inst (.const register value),
        { data with
            instrsMem := wordCseListInsert key register data.instrsMem,
            toCanonical := wordCseInsert register register data.toCanonical,
            toLatest := wordCseInsert register register data.toLatest })

/-- Cake's `word_cseInst`. -/
def wordCseInst [WordCseHash α] (data : WordCseKnowledge) : WordInst α → WordProg α × WordCseKnowledge
  | .const destination value =>
      let data := wordCseInvalidate data destination
      if destination % 2 == 0 then (.inst (.const destination value), data)
      else wordCseAddToDataConst data destination value
  | .arith operation =>
      let register := wordCseFirstRegOfArith operation
      let data := wordCseInvalidateRegs data (wordCseArithWrites operation)
      let adjusted := wordCseCanonicalArith data operation
      let reads := wordCseArithReads adjusted
      /- A fact whose reads include the written register would not describe
         the post-state, so it is not stored. -/
      if wordCseCanMemArith adjusted && !reads.contains register then
        wordCseAddToData (wordCseRegisterReads data reads) register adjusted operation
      else (.inst (.arith operation), data)
  | .mem operator destination address =>
      if wordCseIsStore operator then
        /- A store writes no register but writes memory, so all load facts
           are invalidated; the register-only facts survive. -/
        (.inst (.mem operator destination address), { data with loadsMem := ∅ })
      else
        let data := wordCseInvalidate data destination
        if destination % 2 == 0 || address % 2 == 0 || address = destination then
          (.inst (.mem operator destination address), data)
        else
          let canonicalAddress := wordCseCanonicalRegs' destination data address
          /- `canonicalAddress` is used only for the load fact.  Cake keeps
             the original address in the emitted instruction, preserving any
             explicit materialisation that preceded it. -/
          wordCseAddToLoad (wordCseRegisterRead data canonicalAddress) destination
            (wordCseLoadToNumList operator canonicalAddress)
            (.inst (.mem operator destination address))

  | .memOffset operator destination address offset =>
      if wordCseIsStore operator then
        (.inst (.memOffset operator destination address offset), { data with loadsMem := ∅ })
      else
        let data := wordCseInvalidate data destination
        if destination % 2 == 0 || address % 2 == 0 || address = destination then
          (.inst (.memOffset operator destination address offset), data)
        else
          let canonicalAddress := wordCseCanonicalRegs' destination data address
          wordCseAddToLoad (wordCseRegisterRead data canonicalAddress) destination
            (wordCseLoadOffsetToNumList operator canonicalAddress offset)
            (.inst (.memOffset operator destination address offset))

/-- Cake's `bm_inter_eq`/`inter_eq`, first-order equality intersection. -/
def wordCseInterEq (first second : WordCseRegMap) : WordCseRegMap :=
  first.filter (fun key value => second[key]? == some value)

def wordCseListInterEq (first second : WordCseFactMap) : WordCseFactMap :=
  first.filter (fun key value => second[key]? == some value)

/-- Cake's `merge_data`: the facts that hold after either branch survive, and
    `to_latest` is reset. -/
def wordCseMergeData (first second : WordCseKnowledge) : WordCseKnowledge :=
  { toCanonical := wordCseInterEq first.toCanonical second.toCanonical
    toLatest := ∅
    getsMem := first.getsMem.filter
      (fun key value => second.getsMem[key]? == some value)
    instrsMem := wordCseListInterEq first.instrsMem second.instrsMem
    loadsMem := wordCseListInterEq first.loadsMem second.loadsMem }

def wordCseProg [WordCseHash α] : WordCseKnowledge → WordProg α → WordProg α × WordCseKnowledge
  | data, .skip => (.skip, data)
  | data, .move priority moves =>
      (.move priority moves, wordCseCanonicalMoveRegs data moves)
  | data, .inst instruction => wordCseInst data instruction
  | data, .get destination store =>
      let data := wordCseInvalidate data destination
      match data.getsMem[wordCseStoreCode store]? with
      | none =>
          if destination % 2 == 0 then (.get destination store, data)
          else
            (.get destination store,
              { data with
                  getsMem := data.getsMem.insert (wordCseStoreCode store) destination,
                  toCanonical := wordCseInsert destination destination data.toCanonical,
                  toLatest := wordCseInsert destination destination data.toLatest })
      | some previous =>
          let source := wordCseLookupAny previous data.toLatest previous
          if destination % 2 == 0 then (.move 1 [(destination, source)], data)
          else
            (.move 1 [(destination, source)],
              { data with
                  toCanonical := wordCseInsert destination previous data.toCanonical,
                  toLatest := wordCseInsert previous destination data.toLatest })
  | data, .set store value =>
      if wordCseIsCurrHeap store then (.set store value, wordCseEmpty)
      else
        let getsMem := data.getsMem.erase (wordCseStoreCode store)
        match value with
        | .var source =>
            if source % 2 == 0 then (.set store value, { data with getsMem := getsMem })
            else
              (.set store value,
                { data with
                    getsMem := getsMem.insert (wordCseStoreCode store)
                      (wordCseCanonicalRegs data source)
                    toCanonical := wordCseInsert source
                      (wordCseLookupAny source data.toCanonical source) data.toCanonical })
        | _ => (.set store value, { data with getsMem := getsMem })
  | data, .mustTerminate body =>
      let (body, data) := wordCseProg data body
      (.mustTerminate body, data)
  | _, .call returns target arguments handler =>
      (.call returns target arguments handler, wordCseEmpty)
  | data, .seq first second =>
      let (first, data) := wordCseProg data first
      let (second, data) := wordCseProg data second
      (.seq first second, data)
  | data, .ite operator condition right thenBranch elseBranch =>
      let (thenBranch, thenData) := wordCseProg data thenBranch
      let (elseBranch, elseData) := wordCseProg data elseBranch
      (.ite operator condition right thenBranch elseBranch, wordCseMergeData thenData elseData)
  | data, .opCurrHeap operator destination source =>
      let data := wordCseInvalidate data destination
      /- `source = destination` reads the register the instruction
         overwrites, so such a fact would not describe the post-state. -/
      if source % 2 == 0 || source = destination then
        (.opCurrHeap operator destination source, data)
      else
        let canonicalSource := wordCseCanonicalRegs' destination data source
        /- Cake uses the canonical source only for the fact-table key.  The
           emitted OpCurrHeap retains the source register that was selected
           by instruction selection; this keeps a rematerialised constant
           live through the final dead-code pass. -/
        wordCseAddToFact (wordCseRegisterRead data canonicalSource) data.instrsMem destination
          (wordCseHeapToNumList operator canonicalSource)
          (.opCurrHeap operator destination source)
          (fun data register => wordCseRecordInst data register
            (wordCseHeapToNumList operator canonicalSource))
  | data, .locValue destination source =>
      let data := wordCseInvalidate data destination
      wordCseAddToFact data data.instrsMem destination [48, source]
        (.locValue destination source)
        (fun data register => wordCseRecordInst data register [48, source])
  | data, .store address value =>
      (.store address value, { data with loadsMem := ∅ })
  /- Original word_cse Assign is unconditional identity. Instruction selection
     emits memory loads as mem/memOffset before CSE; an unselected load
     expression must retain its original knowledge and program as well. -/
  | data, .assign name value => (.assign name value, data)
  | data, .raise exception => (.raise exception, data)
  | data, .return label values => (.return label values, data)
  | data, .tick => (.tick, data)
  | _, .alloc destination cutsets => (.alloc destination cutsets, wordCseEmpty)
  | _, .install codeBuffer codeLength dataBuffer dataLength cutsets =>
      (.install codeBuffer codeLength dataBuffer dataLength cutsets, wordCseEmpty)
  | data, .codeBufferWrite address value => (.codeBufferWrite address value, data)
  | data, .dataBufferWrite address value => (.dataBufferWrite address value, data)
  | _, .ffi function configuration configurationLength array arrayLength live =>
      (.ffi function configuration configurationLength array arrayLength live, wordCseEmpty)
  | data, .storeConsts source bitmap codeLength dataLength constants =>
      let data := wordCseInvalidateRegs data [source, bitmap, codeLength, dataLength]
      (.storeConsts source bitmap codeLength dataLength constants,
        { data with loadsMem := ∅ })
  | data, .shareInst operator name address =>
      (.shareInst operator name address,
        if wordCseIsStore operator then data else wordCseInvalidate data name)
  | _, .loop liveIn body liveOut =>
      let (body, _) := wordCseProg wordCseEmpty body
      (.loop liveIn body liveOut, wordCseEmpty)
  | data, .break label => (.break label, data)
  | data, .continue label => (.continue label, data)
termination_by _ program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-- Cake's `word_common_subexp_elim`. -/
def wordCseProp [WordCseHash α] (program : WordProg α) : WordProg α :=
  (wordCseProg wordCseEmpty program).1

end Flapjack.RiscV
