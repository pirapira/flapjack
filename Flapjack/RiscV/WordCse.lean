import Flapjack.Word

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

* the value type `α` is hashed to a `Nat` through `WordCseHash` instead of
  Cake's `wordToNum w = w2n w`, because the port's `WordArith` carries an
  immediate `WordRegImm` instead of Cake's `'a reg_imm`;
* the two `num_map`s, the `store_name` alist and the two balanced maps are
  represented by association lists (`lookupNatInfo` is Cake's `lookup_any`,
  a first-match lookup, and `wordCseInsert` is a replacement insert);
* Cake's balanced-map list keys compare by exact list equality (`listCmp`),
  which is exactly `List` equality here;
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

instance {width : Nat} : WordCseHash (BitVec width) where
  hash value := value.toNat

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

/-- Cake's `knowledge` record.  `toCanonical` and `toLatest` are the two
    register maps, `getsMem` records the register that already holds a store
    value, and `instrsMem`/`loadsMem` are the instruction and load fact
    tables.  Every key is a numeral hash, so the knowledge carries no word
    values. -/
structure WordCseKnowledge where
  toCanonical : List (Nat × Nat)
  toLatest : List (Nat × Nat)
  getsMem : List (Nat × Nat)
  instrsMem : List (List Nat × Nat)
  loadsMem : List (List Nat × Nat)

def wordCseEmpty : WordCseKnowledge :=
  { toCanonical := [], toLatest := [], getsMem := [], instrsMem := [], loadsMem := [] }

/-- Replacement insert, Cake's `num_map` `insert`. -/
def wordCseInsert (key value : Nat) (map : List (Nat × Nat)) : List (Nat × Nat) :=
  (key, value) :: map.filter (fun entry => entry.1 != key)

/-- Replacement insert for the balanced-map keys, which are numeral lists. -/
def wordCseListInsert (key : List Nat) (value : Nat)
    (map : List (List Nat × Nat)) : List (List Nat × Nat) :=
  (key, value) :: map.filter (fun entry => entry.1 != key)

def wordCseListLookup (key : List Nat) (map : List (List Nat × Nat)) : Option Nat :=
  (map.find? (fun entry => entry.1 == key)).map (fun entry => entry.2)

/-- Cake's `lookup_any`: a lookup with a default for missing keys. -/
def wordCseLookupAny (key : Nat) (map : List (Nat × Nat)) (default : Nat) : Nat :=
  (lookupNatInfo key map).getD default

/-- Cake's `map_insert` folds `insert` over the entries so the head of the
    list is inserted last and therefore wins. -/
def wordCseMapInsert (entries : List (Nat × Nat)) (map : List (Nat × Nat)) :
    List (Nat × Nat) :=
  entries.foldr (fun entry accumulated => wordCseInsert entry.1 entry.2 accumulated) map

/-- Cake's `keep_data canon write_to_reg = IS_NONE (lookup write_to_reg canon)`. -/
def wordCseKeepData (data : WordCseKnowledge) (written : Nat) : Bool :=
  (lookupNatInfo written data.toCanonical).isNone

/-- Cake's `invalidate_data`: writing a tracked register discards everything. -/
def wordCseInvalidate (data : WordCseKnowledge) (written : Nat) : WordCseKnowledge :=
  if wordCseKeepData data written then data else wordCseEmpty

def wordCseInvalidateRegs (data : WordCseKnowledge) (written : List Nat) :
    WordCseKnowledge :=
  written.foldl (fun accumulated register => wordCseInvalidate accumulated register) data

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
  /- The five-register two-result primitive has no Cake counterpart and is
     never recorded, so its operands are left alone. -/
  | operation => operation

def wordCseShiftToNum : Shift → Nat
  | .lsl => 40
  | .lsr => 41
  | .asr => 42
  | .ror => 43

def wordCseBinOpToNum : BinOp → Nat
  | .add => 35
  | .sub => 36
  | .and => 37
  | .or => 38
  | .xor => 39

def wordCseRegImmToNumList [WordCseHash α] : WordRegImm α → List Nat
  | .reg register => [33, register + 100]
  | .imm value => [34, WordCseHash.hash value]

def wordCseArithToNumList [WordCseHash α] : WordArith α → List Nat
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
  /- Never stored, so the hash only has to be distinct from the stored
     heads; `can_mem_arith` rejects the five-register primitive. -/
  | .addCarry _ _ _ _ _ => [31]

def wordCseMemOpToNum : WordMemOp → Nat
  | .load => 21
  | .load8 => 22
  | .load16 => 46
  | .load32 => 44
  | .store => 23
  | .store8 => 47
  | .store16 => 24
  | .store32 => 45

/-- Cake's `loadToNumList`.  The port's memory carriers have no immediate
    address offset, so the offset component is `0`. -/
def wordCseLoadToNumList (operator : WordMemOp) (address : Nat) : List Nat :=
  [wordCseMemOpToNum operator, address + 100, 0]

/-- Cake's `instToNumList`.  The `Const` hash deliberately omits the
    destination so that two constants with the same value share a key. -/
def wordCseInstToNumList [WordCseHash α] : WordInst α → List Nat
  | .const _ value => [2, WordCseHash.hash value]
  | .arith operation => 3 :: wordCseArithToNumList operation
  | .mem _ _ _ => [1]

def wordCseIsStore : WordMemOp → Bool
  | .store => true
  | .store8 => true
  | .store16 => true
  | .store32 => true
  | _ => false

def wordCseFirstRegOfArith : WordArith α → Nat
  | .binOp _ destination _ _ => destination
  | .shift _ destination _ _ => destination
  | .div destination _ _ => destination
  | .longMul destinationLeft _ _ _ => destinationLeft
  | .longDiv destinationLeft _ _ _ _ => destinationLeft
  | .cakeAddCarry destination _ _ _ => destination
  | .addCarry destination _ _ _ _ => destination

def wordCseArithWrites : WordArith α → List Nat
  | .binOp _ destination _ _ => [destination]
  | .shift _ destination _ _ => [destination]
  | .div destination _ _ => [destination]
  | .longMul destinationLeft destinationRight _ _ => [destinationLeft, destinationRight]
  | .longDiv destinationLeft destinationRight _ _ _ => [destinationLeft, destinationRight]
  | .cakeAddCarry destination _ _ carry => [destination, carry]
  | .addCarry destination resultCarry _ _ _ => [destination, resultCarry]

def wordCseArithReads : WordArith α → List Nat
  | .binOp _ _ sourceLeft (.reg sourceRight) => [sourceLeft, sourceRight]
  | .binOp _ _ sourceLeft (.imm _) => [sourceLeft]
  | .shift _ _ sourceLeft (.reg sourceRight) => [sourceLeft, sourceRight]
  | .shift _ _ sourceLeft (.imm _) => [sourceLeft]
  | .div _ dividend divisor => [dividend, divisor]
  | .longMul _ _ sourceLeft sourceRight => [sourceLeft, sourceRight]
  | .longDiv _ _ sourceLeft sourceRight quotient => [sourceLeft, sourceRight, quotient]
  | .cakeAddCarry _ sourceLeft sourceRight carry => [sourceLeft, sourceRight, carry]
  | .addCarry _ _ sourceLeft sourceRight carryIn => [sourceLeft, sourceRight, carryIn]

/-- Cake's `can_mem_arith`: only instructions whose operands are odd
    registers (or an odd register with an immediate) may be shared through
    the fact table. -/
def wordCseCanMemArith : WordArith α → Bool
  | .binOp _ _ sourceLeft (.reg sourceRight) =>
      sourceLeft % 2 != 0 && sourceRight % 2 != 0
  | .binOp _ _ sourceLeft (.imm _) => sourceLeft % 2 != 0
  | .div _ dividend divisor => dividend % 2 != 0 && divisor % 2 != 0
  | .shift _ _ destination (.imm _) => destination % 2 != 0
  | _ => false

/-- Cake's `add_to_data_aux`/`add_to_load_aux`, shared by the instruction and
    load fact tables.  `table` is the fact map consulted for a repeated
    instruction and `insert` records the new fact when it is seen first. -/
def wordCseAddToFact (data : WordCseKnowledge) (table : List (List Nat × Nat))
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
        (.inst (.mem operator destination address), { data with loadsMem := [] })
      else
        let data := wordCseInvalidate data destination
        if destination % 2 == 0 || address % 2 == 0 || address = destination then
          (.inst (.mem operator destination address), data)
        else
          let address := wordCseCanonicalRegs' destination data address
          wordCseAddToLoad (wordCseRegisterRead data address) destination
            (wordCseLoadToNumList operator address)
            (.inst (.mem operator destination address))

/-- Cake's `bm_inter_eq`/`inter_eq`, first-order equality intersection. -/
def wordCseInterEq (first second : List (Nat × Nat)) : List (Nat × Nat) :=
  first.filter (fun entry => lookupNatInfo entry.1 second == some entry.2)

def wordCseListInterEq (first second : List (List Nat × Nat)) :
    List (List Nat × Nat) :=
  first.filter (fun entry => wordCseListLookup entry.1 second == some entry.2)

/-- Cake's `merge_data`: the facts that hold after either branch survive, and
    `to_latest` is reset. -/
def wordCseMergeData (first second : WordCseKnowledge) : WordCseKnowledge :=
  { toCanonical := wordCseInterEq first.toCanonical second.toCanonical
    toLatest := []
    getsMem := first.getsMem.filter
      (fun entry => lookupNatInfo entry.1 second.getsMem == some entry.2)
    instrsMem := wordCseListInterEq first.instrsMem second.instrsMem
    loadsMem := wordCseListInterEq first.loadsMem second.loadsMem }

def wordCseProg [WordCseHash α] : WordCseKnowledge → WordProg α → WordProg α × WordCseKnowledge
  | data, .skip => (.skip, data)
  | data, .move priority moves =>
      (.move priority moves, wordCseCanonicalMoveRegs data moves)
  | data, .inst instruction => wordCseInst data instruction
  | data, .get destination store =>
      let data := wordCseInvalidate data destination
      match lookupNatInfo (wordCseStoreCode store) data.getsMem with
      | none =>
          if destination % 2 == 0 then (.get destination store, data)
          else
            (.get destination store,
              { data with
                  getsMem := (wordCseStoreCode store, destination) :: data.getsMem,
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
        let getsMem := data.getsMem.filter
          (fun entry => entry.1 != wordCseStoreCode store)
        match value with
        | .var source =>
            if source % 2 == 0 then (.set store value, { data with getsMem := getsMem })
            else
              (.set store value,
                { data with
                    getsMem := (wordCseStoreCode store, wordCseCanonicalRegs data source) ::
                      getsMem
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
        let source := wordCseCanonicalRegs' destination data source
        wordCseAddToFact (wordCseRegisterRead data source) data.instrsMem destination
          [0, wordCseBinOpToNum operator, source + 100]
          (.opCurrHeap operator destination source)
          (fun data register => wordCseRecordInst data register
            [0, wordCseBinOpToNum operator, source + 100])
  | data, .locValue destination source =>
      let data := wordCseInvalidate data destination
      wordCseAddToFact data data.instrsMem destination [48, source]
        (.locValue destination source)
        (fun data register => wordCseRecordInst data register [48, source])
  | data, .store address value =>
      (.store address value, { data with loadsMem := [] })
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
        { data with loadsMem := [] })
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
