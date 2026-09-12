import Flapjack.Semantics
import Flapjack.Ffi

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

/-! A global-aware full evaluator.  This is intentionally parallel to the
    compact compatibility evaluator below: it provides the CakeML state shape
    needed for the migration of source-to-Crepe correctness without changing
    the existing theorem API in one step. -/
mutual
  def evalCrepFullCallState
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (functions : List (CompiledFunction α))
      (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
      (sharedMem : CrepSharedMemHandler α)
      (baseAddress topAddress : α) :
      Nat → CrepState α →
        Option (List Nat × Option (α × CrepProg α)) → FunName →
        List (CrepExp α) → Option (CrepControlResult α)
    | 0, _, _, _, _ => none
    | fuel + 1, caller, info, function, arguments => do
        let values ← evalCrepFullExpsState caller baseAddress topAddress arguments
        let (parameters, body) ← lookupCompiledFunction function functions
        let calleeLocals ← assignCrepValues (fun _ => none) parameters values
        let callee := CrepState.mk calleeLocals caller.memory caller.globals
        let result ← evalCrepFullProgState functions primitive ffi sharedMem
          baseAddress topAddress fuel callee body
        match result with
        | .normal callee =>
            pure (.normal { caller with
              memory := callee.memory
              globals := callee.globals })
        | .returned callee values =>
            match info with
            | none => pure (.returned { caller with
                memory := callee.memory
                globals := callee.globals } values)
            | some (destinations, _) => do
                let locals ← assignCrepValues caller.locals destinations values
                pure (.normal (CrepState.mk locals callee.memory callee.globals))
        | .raised callee exception =>
            match info with
            | some (_, some (caught, handler)) =>
                if caught == exception then
                  evalCrepFullProgState functions primitive ffi sharedMem
                    baseAddress topAddress fuel
                    (CrepState.mk caller.locals callee.memory callee.globals) handler
                else
                  pure (.raised { caller with
                    memory := callee.memory
                    globals := callee.globals } exception)
            | _ => pure (.raised { caller with
                memory := callee.memory
                globals := callee.globals } exception)
        | .broke callee label =>
            pure (.broke { caller with
              memory := callee.memory
              globals := callee.globals } label)
        | .continued callee label =>
            pure (.continued { caller with
              memory := callee.memory
              globals := callee.globals } label)
        | .finalFfi callee event =>
            pure (.finalFfi { caller with
              locals := fun _ => none
              memory := callee.memory
              globals := callee.globals } event)
    termination_by fuel _ _ _ _ => fuel

  def evalCrepFullProgState
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (functions : List (CompiledFunction α))
      (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
      (sharedMem : CrepSharedMemHandler α)
      (baseAddress topAddress : α) :
      Nat → CrepState α → CrepProg α → Option (CrepControlResult α)
    | 0, _, _ => none
    | _fuel + 1, state, .skip => some (.normal state)
    | fuel + 1, state, .dec name value body => do
        let value ← evalCrepFullExpState state baseAddress topAddress value
        let result ← evalCrepFullProgState functions primitive ffi sharedMem
          baseAddress topAddress fuel
          { state with locals := updateCrepLocal state.locals name value } body
        pure (restoreCrepResult name (state.locals name) result)
    | _fuel + 1, state, .assign name value => do
        let value ← evalCrepFullExpState state baseAddress topAddress value
        pure (.normal { state with locals := updateCrepLocal state.locals name value })
    | _fuel + 1, state, .primitive names operator arguments => do
        let arguments ← arguments.mapM state.locals
        let values ← primitive operator arguments
        let locals ← assignCrepValues state.locals names values
        pure (.normal { state with locals := locals })
    | _fuel + 1, state, .store address value => do
        let address ← evalCrepFullExpState state baseAddress topAddress address
        let value ← evalCrepFullExpState state baseAddress topAddress value
        pure (.normal { state with memory := updateMemory state.memory address value })
    | _fuel + 1, state, .store32 address value
    | _fuel + 1, state, .storeByte address value => do
        let address ← evalCrepFullExpState state baseAddress topAddress address
        let value ← evalCrepFullExpState state baseAddress topAddress value
        pure (.normal { state with memory := updateMemory state.memory address value })
    | _fuel + 1, state, .storeGlob address value => do
        let value ← evalCrepFullExpState state baseAddress topAddress value
        pure (.normal { state with globals := updateMemory state.globals address value })
    | fuel + 1, state, .seq first second => do
        let result ← evalCrepFullProgState functions primitive ffi sharedMem
          baseAddress topAddress fuel state first
        match result with
        | .normal state =>
            evalCrepFullProgState functions primitive ffi sharedMem
              baseAddress topAddress fuel state second
        | result => pure result
    | fuel + 1, state, .ite condition thenBranch elseBranch => do
        let condition ← evalCrepFullExpState state baseAddress topAddress condition
        if condition != 0 then
          evalCrepFullProgState functions primitive ffi sharedMem
            baseAddress topAddress fuel state thenBranch
        else
          evalCrepFullProgState functions primitive ffi sharedMem
            baseAddress topAddress fuel state elseBranch
    | fuel + 1, state, .while conditionExp body => do
        let condition ← evalCrepFullExpState state baseAddress topAddress conditionExp
        if condition == 0 then
          pure (.normal state)
        else
          let result ← evalCrepFullProgState functions primitive ffi sharedMem
            baseAddress topAddress fuel state body
          match result with
          | .normal state | .continued state 0 =>
              evalCrepFullProgState functions primitive ffi sharedMem
                baseAddress topAddress fuel state (.while conditionExp body)
          | .broke state 0 => pure (.normal state)
          | .continued state label => pure (.continued state (label - 1))
          | .broke state label => pure (.broke state (label - 1))
          | result => pure result
    | _fuel + 1, state, .break label => pure (.broke state label)
    | _fuel + 1, state, .continue label => pure (.continued state label)
    | fuel + 1, state, .call info function arguments =>
        evalCrepFullCallState functions primitive ffi sharedMem
          baseAddress topAddress fuel state info function arguments
    | _fuel + 1, state, .extCall function configuration configurationLength array arrayLength => do
        let configuration ← state.locals configuration
        let configurationLength ← state.locals configurationLength
        let array ← state.locals array
        let arrayLength ← state.locals arrayLength
        let ffiResult ← ffi function configuration configurationLength array arrayLength state
        match ffiResult with
        | .returned state => pure (.normal state)
        | .final event => pure (.finalFfi state event)
    | _fuel + 1, state, .raise exception => pure (.raised state exception)
    | _fuel + 1, state, .return values => do
        let values ← evalCrepFullExpsState state baseAddress topAddress values
        pure (.returned state values)
    | _fuel + 1, state, .shMem operator name address => do
        let address ← evalCrepFullExpState state baseAddress topAddress address
        let state ← sharedMem operator name address state
        pure (.normal state)
    | _fuel + 1, state, .tick => pure (.normal state)
    termination_by fuel _ _ => fuel

end

def evalCrepFullResultState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (program : CrepProg α) : Option (List α) :=
  (evalCrepFullProgState functions primitive ffi sharedMem
    baseAddress topAddress fuel state program).bind fun result =>
      match result with
      | .returned _ values => some values
      | .normal _ => some []
      | .raised _ _ | .broke _ _ | .continued _ _ | .finalFfi _ _ => none

theorem evalCrepFullProgState_storeGlob_const
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (address value : α) :
    evalCrepFullProgState [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.storeGlob address (.const value)) =
      some (.normal { state with
        globals := updateMemory state.globals address value }) := by
  simp [evalCrepFullProgState, evalCrepFullExpState]

theorem evalCrepFullProgState_storeGlob_loadGlob
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (address value : α) :
    evalCrepFullProgState [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 2) state
      (.seq (.storeGlob address (.const value))
        (.return [.loadGlob address])) =
      some (.returned { state with
        globals := updateMemory state.globals address value } [value]) := by
  simp [evalCrepFullProgState, evalCrepFullExpState, evalCrepFullExpsState,
    updateMemory]

mutual
  def evalCrepFullCall
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (functions : List (CompiledFunction α))
      (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
      (sharedMem : CrepSharedMemHandler α)
      (baseAddress topAddress : α) :
      Nat → CrepState α →
        Option (List Nat × Option (α × CrepProg α)) → FunName →
        List (CrepExp α) → Option (CrepControlResult α)
    | 0, _, _, _, _ => none
    | fuel + 1, caller, info, function, arguments => do
        let values ← evalCrepFullExps caller.locals caller.memory
          baseAddress topAddress arguments
        let (parameters, body) ← lookupCompiledFunction function functions
        let calleeLocals ← assignCrepValues (fun _ => none) parameters values
        let callee := { locals := calleeLocals, memory := caller.memory }
        let result ← evalCrepFullProg functions primitive ffi sharedMem
          baseAddress topAddress fuel callee body
        match result with
        | .normal callee =>
            pure (.normal { caller with memory := callee.memory })
        | .returned callee values =>
            match info with
            | none => pure (.returned { caller with memory := callee.memory } values)
            | some (destinations, _) => do
                let locals ← assignCrepValues caller.locals destinations values
                pure (.normal { locals := locals, memory := callee.memory })
        | .raised callee exception =>
            match info with
            | some (_, some (caught, handler)) =>
                if caught == exception then
                  evalCrepFullProg functions primitive ffi sharedMem
                    baseAddress topAddress fuel
                    { locals := caller.locals, memory := callee.memory } handler
                else
                  pure (.raised { caller with memory := callee.memory } exception)
            | _ => pure (.raised { caller with memory := callee.memory } exception)
        | .broke callee label =>
            pure (.broke { caller with memory := callee.memory } label)
        | .continued callee label =>
            pure (.continued { caller with memory := callee.memory } label)
        | .finalFfi callee event =>
            pure (.finalFfi { caller with
              locals := fun _ => none
              memory := callee.memory } event)
    termination_by fuel _ _ _ _ => fuel

  def evalCrepFullProg
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (functions : List (CompiledFunction α))
      (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
      (sharedMem : CrepSharedMemHandler α)
      (baseAddress topAddress : α) :
      Nat → CrepState α → CrepProg α → Option (CrepControlResult α)
    | 0, _, _ => none
    | _fuel + 1, state, .skip => some (.normal state)
    | fuel + 1, state, .dec name value body => do
        let value ← evalCrepFullExp state.locals state.memory baseAddress topAddress value
        let result ← evalCrepFullProg functions primitive ffi sharedMem
          baseAddress topAddress fuel
          { state with locals := updateCrepLocal state.locals name value } body
        pure (restoreCrepResult name (state.locals name) result)
    | _fuel + 1, state, .assign name value => do
        let value ← evalCrepFullExp state.locals state.memory baseAddress topAddress value
        pure (.normal { state with locals := updateCrepLocal state.locals name value })
    | _fuel + 1, state, .primitive names operator arguments => do
        let arguments ← arguments.mapM state.locals
        let values ← primitive operator arguments
        let locals ← assignCrepValues state.locals names values
        pure (.normal { state with locals := locals })
    | _fuel + 1, state, .store address value => do
        let address ← evalCrepFullExp state.locals state.memory baseAddress topAddress address
        let value ← evalCrepFullExp state.locals state.memory baseAddress topAddress value
        pure (.normal { state with memory := updateMemory state.memory address value })
    | _fuel + 1, state, .store32 address value
    | _fuel + 1, state, .storeByte address value => do
        let address ← evalCrepFullExp state.locals state.memory baseAddress topAddress address
        let value ← evalCrepFullExp state.locals state.memory baseAddress topAddress value
        pure (.normal { state with memory := updateMemory state.memory address value })
    | _fuel + 1, state, .storeGlob address value => do
        let value ← evalCrepFullExp state.locals state.memory baseAddress topAddress value
        pure (.normal { state with memory := updateMemory state.memory address value })
    | fuel + 1, state, .seq first second => do
        let result ← evalCrepFullProg functions primitive ffi sharedMem
          baseAddress topAddress fuel state first
        match result with
        | .normal state =>
            evalCrepFullProg functions primitive ffi sharedMem
              baseAddress topAddress fuel state second
        | result => pure result
    | fuel + 1, state, .ite condition thenBranch elseBranch => do
        let condition ← evalCrepFullExp state.locals state.memory baseAddress topAddress condition
        if condition != 0 then
          evalCrepFullProg functions primitive ffi sharedMem
            baseAddress topAddress fuel state thenBranch
        else
          evalCrepFullProg functions primitive ffi sharedMem
            baseAddress topAddress fuel state elseBranch
    | fuel + 1, state, .while conditionExp body => do
        let condition ← evalCrepFullExp state.locals state.memory baseAddress topAddress conditionExp
        if condition == 0 then
          pure (.normal state)
        else
          let result ← evalCrepFullProg functions primitive ffi sharedMem
            baseAddress topAddress fuel state body
          match result with
          | .normal state | .continued state 0 =>
              evalCrepFullProg functions primitive ffi sharedMem
                baseAddress topAddress fuel state (.while conditionExp body)
          | .broke state 0 => pure (.normal state)
          | .continued state label => pure (.continued state (label - 1))
          | .broke state label => pure (.broke state (label - 1))
          | result => pure result
    | _fuel + 1, state, .break label => pure (.broke state label)
    | _fuel + 1, state, .continue label => pure (.continued state label)
    | fuel + 1, state, .call info function arguments =>
        evalCrepFullCall functions primitive ffi sharedMem
          baseAddress topAddress fuel state info function arguments
    | _fuel + 1, state, .extCall function configuration configurationLength array arrayLength => do
        let configuration ← state.locals configuration
        let configurationLength ← state.locals configurationLength
        let array ← state.locals array
        let arrayLength ← state.locals arrayLength
        let ffiResult ← ffi function configuration configurationLength array arrayLength state
        match ffiResult with
        | .returned state => pure (.normal state)
        | .final event => pure (.finalFfi state event)
    | _fuel + 1, state, .raise exception => pure (.raised state exception)
    | _fuel + 1, state, .return values => do
        let values ← evalCrepFullExps state.locals state.memory
          baseAddress topAddress values
        pure (.returned state values)
    | _fuel + 1, state, .shMem operator name address => do
        let address ← evalCrepFullExp state.locals state.memory baseAddress topAddress address
        let state ← sharedMem operator name address state
        pure (.normal state)
    | _fuel + 1, state, .tick => pure (.normal state)
    termination_by fuel _ _ => fuel
end

theorem evalCrepFullProg_extCall [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state state' : CrepState α) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some state') :
    evalCrepFullProg functions primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state
      (.extCall function configuration configurationLength array arrayLength) =
      some (.normal state') := by
  simp [evalCrepFullProg, hconfiguration, hconfigurationLength, harray,
    harrayLength, hffi]

theorem evalCrepFullProg_extCall_finalFfi [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (event : FfiFinalEvent)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some (.final event)) :
    evalCrepFullProg functions primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state
      (.extCall function configuration configurationLength array arrayLength) =
      some (.finalFfi state event) := by
  simp [evalCrepFullProg, hconfiguration, hconfigurationLength, harray,
    harrayLength, hffi]

theorem evalCrepFullCall_caught_handler [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (function : FunName)
    (destinations : List Nat) (caught : α) (handler : CrepProg α)
    (arguments : List (CrepExp α)) (values : List α)
    (parameters : List Nat) (body : CrepProg α)
    (calleeLocals : Nat → Option α) (callee : CrepState α)
    (exception : α) (result : CrepControlResult α)
    (hvalues : evalCrepFullExps caller.locals caller.memory
      baseAddress topAddress arguments = some values)
    (hlookup : lookupCompiledFunction function functions = some (parameters, body))
    (hassign : assignCrepValues (fun _ => none) parameters values =
      some calleeLocals)
    (hcallee : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := calleeLocals, memory := caller.memory } body =
      some (.raised callee exception))
    (hcaught : caught == exception)
    (hhandler : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := caller.locals, memory := callee.memory } handler =
      some result) :
    evalCrepFullCall functions primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) caller (some (destinations, some (caught, handler))) function
      arguments = some result := by
  simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee, hcaught,
    hhandler]

theorem evalCrepFullCall_uncaught [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (function : FunName)
    (arguments : List (CrepExp α)) (values : List α)
    (parameters : List Nat) (body : CrepProg α)
    (calleeLocals : Nat → Option α) (callee : CrepState α)
    (exception : α)
    (hvalues : evalCrepFullExps caller.locals caller.memory
      baseAddress topAddress arguments = some values)
    (hlookup : lookupCompiledFunction function functions = some (parameters, body))
    (hassign : assignCrepValues (fun _ => none) parameters values =
      some calleeLocals)
    (hcallee : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := calleeLocals, memory := caller.memory } body =
      some (.raised callee exception)) :
    evalCrepFullCall functions primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) caller none function arguments =
      some (.raised { caller with memory := callee.memory } exception) := by
  simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee]

def evalCrepFullResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (program : CrepProg α) : Option (List α) :=
  (evalCrepFullProg functions primitive ffi sharedMem
    baseAddress topAddress fuel state program).bind fun result =>
      match result with
      | .returned _ values => some values
      | .normal _ => some []
      | .raised _ _ | .broke _ _ | .continued _ _ | .finalFfi _ _ => none

end Flapjack
