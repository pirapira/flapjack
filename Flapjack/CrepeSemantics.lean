import Flapjack.Semantics
import Flapjack.Ffi
import Flapjack.PanMemoryModel

/-!
Fuel-bounded executable semantics for the full scalar Crepe control fragment.

The smaller evaluators in `Semantics.lean` are useful for local equations and
for the first call regression, but they intentionally omit memory, loops,
handlers, and foreign actions.  This evaluator keeps those effects together
in one state so that a source-to-Crepe simulation can be stated without
changing semantic representations between individual constructors.
-/

namespace Flapjack

def evalCrepFullExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α) : CrepExp α → Option α
  | .const value => some value
  | .var name => locals name
  | .load address | .load32 address | .loadByte address => do
      let address ← evalCrepFullExp locals memory baseAddress topAddress address
      memory address
  | .loadGlob address => memory address
  | .op operator [left, right] => do
      let left ← evalCrepFullExp locals memory baseAddress topAddress left
      let right ← evalCrepFullExp locals memory baseAddress topAddress right
      pure (evalPanBinOp operator left right)
  | .crepOp .mul [left, right] => do
      let left ← evalCrepFullExp locals memory baseAddress topAddress left
      let right ← evalCrepFullExp locals memory baseAddress topAddress right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalCrepFullExp locals memory baseAddress topAddress left
      let right ← evalCrepFullExp locals memory baseAddress topAddress right
      pure (evalPanCmp operator left right)
  | .shift operator left right => do
      let left ← evalCrepFullExp locals memory baseAddress topAddress left
      let right ← evalCrepFullExp locals memory baseAddress topAddress right
      evalPanShift operator left right
  | .baseAddr => some baseAddress
  | .topAddr => some topAddress
  | _ => none
termination_by expression => sizeOf expression

def evalCrepFullExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α) : List (CrepExp α) → Option (List α)
  | [] => some []
  | expression :: expressions => do
      let value ← evalCrepFullExp locals memory baseAddress topAddress expression
      let values ← evalCrepFullExps locals memory baseAddress topAddress expressions
      pure (value :: values)
termination_by expressions => sizeOf expressions

structure CrepState (α : Type u) where
  locals : Nat → Option α
  memory : α → Option α
  /-- Global words are kept separate from ordinary memory, as in CakeML's
      `crepSem` state.  The default preserves the compact-state API for
      localized programs. -/
  globals : α → Option α := fun _ => none

/-! Canonical checked word-cell memory boundary.

    This is the Lean counterpart of the memory portion of CakeML's
    `crepSem.state`.  In particular, the domain is separate from the partial
    Lean memory map, and byte/32-bit accesses are delegated to the target
    model with explicit endianness.  The legacy evaluators below intentionally
    remain unchanged until their callers are migrated to this boundary. -/
structure CrepMemoryState (α : Type u) where
  memory : PanWordMemory α
  memaddrs : PanWordMemoryDomain α
  bytesInWord : α
  bigEndian : Bool
  model : PanMemoryModel α

def crepMemLoad (state : CrepMemoryState α) (address : α) : Option α :=
  panModelReadWord state.memaddrs state.memory address

def crepMemStore [BEq α] (state : CrepMemoryState α)
    (address value : α) : Option (CrepMemoryState α) :=
  (panModelStoreWord state.memaddrs state.memory address value).map
    (fun memory => { state with memory := memory })

def crepMemLoadByte [Add α] [OfNat α 1]
    (state : CrepMemoryState α) (address : α) : Option α :=
  panModelReadByte state.model state.memaddrs state.memory
    state.bytesInWord address state.bigEndian

def crepMemStoreByte [BEq α] [Add α] [OfNat α 1]
    (state : CrepMemoryState α) (address value : α) :
    Option (CrepMemoryState α) :=
  (panModelStoreByte state.model state.memaddrs state.memory
    state.bytesInWord address value state.bigEndian).map
    (fun memory => { state with memory := memory })

def crepMemLoad32 [Add α] [OfNat α 1] [OfNat α 2] [OfNat α 3]
    (state : CrepMemoryState α) (address : α) : Option α :=
  panModelRead32 state.model state.memaddrs state.memory
    state.bytesInWord address state.bigEndian

def crepMemStore32 [BEq α] [Add α] [OfNat α 0] [OfNat α 1]
    [OfNat α 2] [OfNat α 3]
    (state : CrepMemoryState α) (address value : α) :
    Option (CrepMemoryState α) :=
  (panModelStore32 state.model state.memaddrs state.memory
    state.bytesInWord address value state.bigEndian).map
    (fun memory => { state with memory := memory })

theorem crepMemLoad_none_of_not_memaddr
    (state : CrepMemoryState α) (address : α)
    (haddress : state.memaddrs address = false) :
    crepMemLoad state address = none := by
  simp [crepMemLoad, panModelReadWord, haddress]

theorem crepMemStore_none_of_not_memaddr [BEq α]
    (state : CrepMemoryState α) (address value : α)
    (haddress : state.memaddrs address = false) :
    crepMemStore state address value = none := by
  simp [crepMemStore, panModelStoreWord, haddress]

theorem crepMemStore_memory_of_memaddr [BEq α]
    (state : CrepMemoryState α) (address value : α)
    (haddress : state.memaddrs address = true) :
    crepMemStore state address value =
      some { state with memory := panModelUpdateMemory state.memory address value } := by
  simp [crepMemStore, panModelStoreWord, haddress]

inductive CrepControlResult (α : Type u) where
  | normal (state : CrepState α)
  | returned (state : CrepState α) (values : List α)
  | raised (state : CrepState α) (exception : α)
  | broke (state : CrepState α) (label : Nat)
  | continued (state : CrepState α) (label : Nat)
  | finalFfi (state : CrepState α) (event : FfiFinalEvent)

inductive CrepFfiResult (α : Type u) where
  | returned (state : CrepState α)
  | final (event : FfiFinalEvent)

instance : Coe (CrepState α) (CrepFfiResult α) :=
  ⟨CrepFfiResult.returned⟩

abbrev CrepFfiHandler (α : Type u) :=
  FunName → α → α → α → α → CrepState α → Option (CrepFfiResult α)

abbrev CrepSharedMemHandler (α : Type u) :=
  CrepMemOp → Nat → α → CrepState α → Option (CrepState α)

def restoreCrepLocal (locals : Nat → Option α) (name : Nat)
    (oldValue : Option α) : Nat → Option α :=
  fun current => if current = name then oldValue else locals current

def restoreCrepResult (name : Nat) (oldValue : Option α) :
    CrepControlResult α → CrepControlResult α
  | .normal state => .normal { state with locals := restoreCrepLocal state.locals name oldValue }
  | .returned state values =>
      .returned { state with locals := restoreCrepLocal state.locals name oldValue } values
  | .raised state exception =>
      .raised { state with locals := restoreCrepLocal state.locals name oldValue } exception
  | .broke state label =>
      .broke { state with locals := restoreCrepLocal state.locals name oldValue } label
  | .continued state label =>
      .continued { state with locals := restoreCrepLocal state.locals name oldValue } label
  | .finalFfi state event =>
      .finalFfi { state with locals := restoreCrepLocal state.locals name oldValue } event

def defaultCrepSharedMemHandler [BEq α]
    : CrepSharedMemHandler α :=
  fun operator name address state =>
    match operator with
    | .load | .load8 | .load16 | .load32 => do
        let value ← state.memory address
        pure { state with locals := updateCrepLocal state.locals name value }
    | .store | .store8 | .store16 | .store32 => do
        let value ← state.locals name
        pure { state with memory := updateMemory state.memory address value }

def noCrepFfi (α : Type u) : CrepFfiHandler α :=
  fun _ _ _ _ _ _ => none

/-! State-aware expression evaluation for the forthcoming global-aware full
    evaluator.  The existing compact evaluator remains available while the
    source-to-Crep proof suite is migrated in smaller slices. -/
def evalCrepFullExpState [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α) : CrepExp α → Option α
  | .const value => some value
  | .var name => state.locals name
  | .load address | .load32 address | .loadByte address => do
      let address ← evalCrepFullExpState state baseAddress topAddress address
      state.memory address
  | .loadGlob address => state.globals address
  | .op operator [left, right] => do
      let left ← evalCrepFullExpState state baseAddress topAddress left
      let right ← evalCrepFullExpState state baseAddress topAddress right
      pure (evalPanBinOp operator left right)
  | .crepOp .mul [left, right] => do
      let left ← evalCrepFullExpState state baseAddress topAddress left
      let right ← evalCrepFullExpState state baseAddress topAddress right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalCrepFullExpState state baseAddress topAddress left
      let right ← evalCrepFullExpState state baseAddress topAddress right
      pure (evalPanCmp operator left right)
  | .shift operator left right => do
      let left ← evalCrepFullExpState state baseAddress topAddress left
      let right ← evalCrepFullExpState state baseAddress topAddress right
      evalPanShift operator left right
  | .baseAddr => some baseAddress
  | .topAddr => some topAddress
  | _ => none
termination_by expression => sizeOf expression

/-! Target-word state evaluation with CakeML's complete `word_sh` semantics.

    The legacy evaluator above remains the compatibility entrypoint for the
    abstract fragment. RISC-V stateful callers use this boundary so ASR/ROR
    are not silently turned into `none`, and shift counts at or above the word
    width retain Cake's failure behavior. -/
def evalCrepFullExpStateFull [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α) : CrepExp α → Option α
  | .const value => some value
  | .var name => state.locals name
  | .load address | .load32 address | .loadByte address => do
      let address ← evalCrepFullExpStateFull state baseAddress topAddress address
      state.memory address
  | .loadGlob address => state.globals address
  | .op operator [left, right] => do
      let left ← evalCrepFullExpStateFull state baseAddress topAddress left
      let right ← evalCrepFullExpStateFull state baseAddress topAddress right
      pure (evalPanBinOp operator left right)
  | .crepOp .mul [left, right] => do
      let left ← evalCrepFullExpStateFull state baseAddress topAddress left
      let right ← evalCrepFullExpStateFull state baseAddress topAddress right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalCrepFullExpStateFull state baseAddress topAddress left
      let right ← evalCrepFullExpStateFull state baseAddress topAddress right
      pure (evalPanCmp operator left right)
  | .shift operator left right => do
      let left ← evalCrepFullExpStateFull state baseAddress topAddress left
      let right ← evalCrepFullExpStateFull state baseAddress topAddress right
      evalPanShiftFull operator left right
  | .baseAddr => some baseAddress
  | .topAddr => some topAddress
  | _ => none
termination_by expression => sizeOf expression

/-! Checked target-word expression boundary.  Unlike the compatibility
    evaluator above, this entrypoint consumes `CrepMemoryState`, so ordinary
    loads, byte loads, and 32-bit loads go through Cake's domain/alignment,
    endian, and word-cell operations. -/
def evalCrepCheckedExpStateFull
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [OfNat α 2] [OfNat α 3]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (globals : α → Option α)
    (memoryState : CrepMemoryState α)
    (baseAddress topAddress : α) : CrepExp α → Option α
  | .const value => some value
  | .var name => locals name
  | .load address => do
      let address ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress address
      crepMemLoad memoryState address
  | .load32 address => do
      let address ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress address
      crepMemLoad32 memoryState address
  | .loadByte address => do
      let address ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress address
      crepMemLoadByte memoryState address
  | .loadGlob address => globals address
  | .op operator [left, right] => do
      let left ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress left
      let right ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress right
      pure (evalPanBinOp operator left right)
  | .crepOp .mul [left, right] => do
      let left ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress left
      let right ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress left
      let right ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress right
      pure (evalPanCmp operator left right)
  | .shift operator left right => do
      let left ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress left
      let right ← evalCrepCheckedExpStateFull locals globals memoryState
        baseAddress topAddress right
      evalPanShiftFull operator left right
  | .baseAddr => some baseAddress
  | .topAddr => some topAddress
  | _ => none
termination_by expression => sizeOf expression

def evalCrepFullExpsStateFull [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α) :
    List (CrepExp α) → Option (List α)
  | [] => some []
  | expression :: expressions => do
      let value ← evalCrepFullExpStateFull state baseAddress topAddress expression
      let values ← evalCrepFullExpsStateFull state baseAddress topAddress expressions
      pure (value :: values)
termination_by expressions => sizeOf expressions

def evalCrepFullExpsState [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α) :
    List (CrepExp α) → Option (List α)
  | [] => some []
  | expression :: expressions => do
      let value ← evalCrepFullExpState state baseAddress topAddress expression
      let values ← evalCrepFullExpsState state baseAddress topAddress expressions
      pure (value :: values)
termination_by expressions => sizeOf expressions

/-! Syntactic support for migrating localized expression proofs.  Compiled
    expressions in the localized source fragment cannot contain `loadGlob`;
    this predicate makes that fact an explicit premise of the compatibility
    theorem below. -/
inductive CrepExpNoGlobal {α : Type u} : CrepExp α → Prop where
  | const (value : α) : CrepExpNoGlobal (.const value)
  | var (name : Nat) : CrepExpNoGlobal (.var name)
  | load {address : CrepExp α} :
      CrepExpNoGlobal address → CrepExpNoGlobal (.load address)
  | load32 {address : CrepExp α} :
      CrepExpNoGlobal address → CrepExpNoGlobal (.load32 address)
  | loadByte {address : CrepExp α} :
      CrepExpNoGlobal address → CrepExpNoGlobal (.loadByte address)
  | op {operator : BinOp} {left right : CrepExp α} :
      CrepExpNoGlobal left → CrepExpNoGlobal right →
      CrepExpNoGlobal (.op operator [left, right])
  | crepMul {left right : CrepExp α} :
      CrepExpNoGlobal left → CrepExpNoGlobal right →
      CrepExpNoGlobal (.crepOp .mul [left, right])
  | cmp {operator : Cmp} {left right : CrepExp α} :
      CrepExpNoGlobal left → CrepExpNoGlobal right →
      CrepExpNoGlobal (.cmp operator left right)
  | shift {operator : Shift} {left right : CrepExp α} :
      CrepExpNoGlobal left → CrepExpNoGlobal right →
      CrepExpNoGlobal (.shift operator left right)
  | baseAddr : CrepExpNoGlobal (.baseAddr : CrepExp α)
  | topAddr : CrepExpNoGlobal (.topAddr : CrepExp α)

theorem evalCrepFullExpState_eq_of_noGlobal
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α)
    (expression : CrepExp α) (hnoGlobal : CrepExpNoGlobal expression) :
    evalCrepFullExpState state baseAddress topAddress expression =
      evalCrepFullExp state.locals state.memory baseAddress topAddress expression := by
  induction hnoGlobal with
  | const => simp [evalCrepFullExpState, evalCrepFullExp]
  | var => simp [evalCrepFullExpState, evalCrepFullExp]
  | load hnoGlobal ih =>
      simp [evalCrepFullExpState, evalCrepFullExp, ih]
  | load32 hnoGlobal ih =>
      simp [evalCrepFullExpState, evalCrepFullExp, ih]
  | loadByte hnoGlobal ih =>
      simp [evalCrepFullExpState, evalCrepFullExp, ih]
  | op hleft hright ihLeft ihRight =>
      simp [evalCrepFullExpState, evalCrepFullExp, ihLeft, ihRight]
  | crepMul hleft hright ihLeft ihRight =>
      simp [evalCrepFullExpState, evalCrepFullExp, ihLeft, ihRight]
  | cmp hleft hright ihLeft ihRight =>
      simp [evalCrepFullExpState, evalCrepFullExp, ihLeft, ihRight]
  | shift hleft hright ihLeft ihRight =>
      simp [evalCrepFullExpState, evalCrepFullExp, ihLeft, ihRight]
  | baseAddr => simp [evalCrepFullExpState, evalCrepFullExp]
  | topAddr => simp [evalCrepFullExpState, evalCrepFullExp]

theorem evalCrepFullExpsState_eq_of_noGlobals
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α)
    (expressions : List (CrepExp α))
    (hnoGlobal : ∀ expression ∈ expressions, CrepExpNoGlobal expression) :
    evalCrepFullExpsState state baseAddress topAddress expressions =
      evalCrepFullExps state.locals state.memory baseAddress topAddress expressions := by
  induction expressions with
  | nil => simp [evalCrepFullExpsState, evalCrepFullExps]
  | cons expression expressions ih =>
      have hexpression := hnoGlobal expression (by simp)
      have htail : ∀ current ∈ expressions, CrepExpNoGlobal current := by
        intro current hcurrent
        exact hnoGlobal current (by simp [hcurrent])
      simp [evalCrepFullExpsState, evalCrepFullExps,
        evalCrepFullExpState_eq_of_noGlobal state baseAddress topAddress
          expression hexpression,
        ih htail]

/-- Counterpart of Cake `crepProps$lookup_locals_eq_map_vars`
    (`cakeml/pancake/semantics/crepPropsScript.sml`): reading a list of local
    variables through `OPT_MMAP` of the local map equals evaluating the
    corresponding `.var` expressions. -/
theorem lookup_locals_eq_map_vars
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepState α) (baseAddress topAddress : α) (names : List Nat) :
    names.mapM state.locals =
      (names.map (CrepExp.var (α := α))).mapM
        (evalCrepFullExpState state baseAddress topAddress) := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp [evalCrepFullExpState, ih]

end Flapjack
