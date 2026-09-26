import Flapjack.CrepeSemantics
import Flapjack.FiniteMap.Basic
import Flapjack.HolRef
import Flapjack.PanValueFfiSemantics

/-!
Observable runtime boundary for the Crepe evaluator.

`CrepeSemantics` is intentionally a compact executable model whose handlers
return either a new state or an observable terminal event.  CakeML's `crepSem`
has a richer machine state and the same observable `FinalFFI` result.  This
file ports that richer runtime boundary: it is the state/result vocabulary on
which the full compiler simulation can be built.

The FFI request carries the byte arrays produced by CakeML's
`read_bytearray`.  A handler receives only the concrete `FfiState` and may
return only its successor plus bytes, matching CakeML's `call_FFI` boundary;
the runtime itself applies the prescribed memory/local updates.  The runtime
still keeps the memory domains, clock, endianness, and FFI state explicit.
-/

namespace Flapjack

/- A tiny Nat word-cell model used by the executable runtime fixtures.  The
   production evaluator receives a target's `PanMemoryModel`; this fixture
   keeps the existing Nat regression states explicit without smuggling in a
   whole target backend. -/
def natCrepRuntimeMemoryModel : PanMemoryModel Nat :=
  { byteAlign := fun _ address => address
    getByte := fun _ _ value _ => value
    setByte := fun _ _ value _ _ => value
    aligned := fun _ _ => true
    wordOfBytes := fun _ bytes =>
      match bytes with
      | value :: _ => value
      | [] => 0
    wordOp := fun operator values =>
      match operator with
      | .add => some (values.foldr (fun left right => left + right) 0)
      | .sub =>
          match values with
          | [left, right] => some (left - right)
          | _ => none
      | .and | .or | .xor => none
    compare := fun operator left right => evalPanCmp operator left right
    shift := fun operator left right => evalPanShift operator left right }

def natCrepRuntimeFfiContext : PanValueFfiContext Nat :=
  { sharedDomain := fun _ => true
    byteAlign := fun address => address
    bigEndian := false
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes =>
      match bytes with
      | value :: _ => value.toNat
      | [] => 0
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun value => value.toNat
    valueToNat := id }

def natCrepRuntimeFfiOracle : FfiOracle Unit :=
  fun _ state _ bytes => .returned state bytes

def natCrepRuntimeFfiState : FfiState Unit :=
  { oracle := natCrepRuntimeFfiOracle
    state := ()
    ioEvents := [] }

structure CrepRuntimeState (α σ : Type u) where
  /-- HOL `crepSem$state.locals` is a finite map from `varname` to `word_lab`.
      Lean's function representation is extensionally the same finite map;
      `PanWordLab.word` retains the HOL cell wrapper. -/
  locals : Nat → Option (PanWordLab α)
  /-- HOL `crepSem$state.globals` is a finite map from `5 word` to `word_lab`.
      Lean's function representation is extensionally the same finite map;
      `PanWordLab.word` retains the HOL cell wrapper. -/
  globals : BitVec 5 → Option (PanWordLab α)
  /-- HOL `crepSem$state.code`: the code map used by runtime function calls. -/
  code : FunName → Option (List Nat × CrepProg α)
  /-- HOL `crepSem$state.memory` is a total `'a word → 'a word_lab` function
      guarded by `memaddrs`; `PanWordLab.word` retains the HOL cell wrapper. -/
  memory : α → PanWordLab α
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  /-- The word-cell operations used by CakeML's `mem_load_byte` and
      `mem_load_32` (panSemScript.sml:86-137). -/
  memoryModel : PanMemoryModel α
  bytesInWord : α
  ffiContext : PanValueFfiContext α
  clock : Nat
  bigEndian : Bool
  ffi : FfiState σ
  baseAddress : α
  topAddress : α

/-- Flapjack's field-only encoding of HOL `crepSem$state` for a fixed
    `RiscV.Word width` carrier. Finite maps are represented extensionally by
    lookup functions, and the three target-configuration fields
    (`memoryModel`, `bytesInWord`, `ffiContext`) of the executable
    `CrepRuntimeState` are absent, matching HOL's 11-field state. It is
    untagged because it does not quantify over HOL's arbitrary word carrier. -/
structure CrepHolState (α σ : Type u) where
  locals : Nat → Option (PanWordLab α)
  globals : BitVec 5 → Option (PanWordLab α)
  code : FunName → Option (List Nat × CrepProg α)
  memory : α → PanWordLab α
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  clock : Nat
  bigEndian : Bool
  ffi : FfiState σ
  baseAddress : α
  topAddress : α

/-! Source-shaped Crep memory-read helpers, parameterized by the word
    operations for one particular word carrier. These make the case split in
    HOL `panSem$mem_load_byte_def` and the alignment/domain/list computation in
    `mem_load_32_def` explicit before adapting the `word32` result back to the
    state's word type. The extra `PanMemoryModel` and `bytesInWord` parameters
    stand for operations fixed by HOL's word type; until their generic
    correspondence is established these helpers are Flapjack infrastructure
    and carry no HOL tag. -/
def crepHolEvalMemLoadByte
    (model : PanMemoryModel α) (bytesInWord : α)
    (state : CrepHolState α σ) (address : α) : Option α :=
  let alignedAddress := model.byteAlign bytesInWord address
  match state.memory alignedAddress with
  | .word value =>
      if state.memaddrs alignedAddress then
        some (model.getByte bytesInWord address value state.bigEndian)
      else none

def crepHolEvalMemLoad32 [Add α] [OfNat α 1] [OfNat α 2] [OfNat α 3]
    (model : PanMemoryModel α) (bytesInWord : α)
    (state : CrepHolState α σ) (address : α) : Option α :=
  if model.aligned 4 address then
    let alignedAddress := model.byteAlign bytesInWord address
    match state.memory alignedAddress with
    | .word value =>
        if state.memaddrs alignedAddress then
          some (model.wordOfBytes32 state.bigEndian
            [model.getByte bytesInWord address value state.bigEndian,
             model.getByte bytesInWord (address + 1) value state.bigEndian,
             model.getByte bytesInWord (address + 2) value state.bigEndian,
             model.getByte bytesInWord (address + 3) value state.bigEndian])
        else none
  else none

theorem crepHolEvalMemLoadByte_eq_panModelReadByte [Add α] [OfNat α 1]
    (model : PanMemoryModel α) (bytesInWord : α)
    (state : CrepHolState α σ) (address : α) :
    crepHolEvalMemLoadByte model bytesInWord state address =
      panModelReadByte model state.memaddrs
        (fun current => some (panTheWord (state.memory current)))
        bytesInWord address state.bigEndian := by
  unfold crepHolEvalMemLoadByte panModelReadByte
  cases hcell : state.memory (model.byteAlign bytesInWord address)
  simp [hcell, panTheWord]

theorem crepHolEvalMemLoad32_eq_panModelRead32 [Add α]
    [OfNat α 1] [OfNat α 2] [OfNat α 3]
    (model : PanMemoryModel α) (bytesInWord : α)
    (state : CrepHolState α σ) (address : α) :
    crepHolEvalMemLoad32 model bytesInWord state address =
      panModelRead32 model state.memaddrs
        (fun current => some (panTheWord (state.memory current)))
        bytesInWord address state.bigEndian := by
  unfold crepHolEvalMemLoad32 panModelRead32
  by_cases haligned : model.aligned 4 address
  · simp only [haligned, ↓reduceIte]
    cases hcell : state.memory (model.byteAlign bytesInWord address)
    simp [hcell, panTheWord]
  · simp [haligned]

/-- Generic production global update on the 11-field `CrepHolState`.
    HOL `crepSem$set_globals_def` (`crepSemScript.sml:61`) is word-length
    indexed (`'a crepSem$state`), so the generic-`α` form is deliberately
    UNTAGGED (a generic parameter is not the fixed HOL word carrier); the
    width-indexed counterpart is `setCrepHolGlobalsW` below (also untagged:
    the whole-state carrier still admits infinite-support `locals`/`code`).
    Production `setCrepRuntimeGlobals` routes its globals update through this
    definition while preserving its three extra configuration fields. -/
def setCrepHolGlobals (key : BitVec 5) (value : PanWordLab α)
    (state : CrepHolState α σ) : CrepHolState α σ :=
  { state with globals := FUPDATE state.globals (key, value) }

/-! FLAPJACK-SPECIFIC (not a statement-exact HOL port): the clause
    `set_globals gv w s = s with globals := s.globals |+ (gv,w)` is HOL's
    (`crepSemScript.sml:61`), and the field it updates (`globals : BitVec 5 →
    Option _`) is finite by type, but the carrier `CrepHolState (BitVec width) σ`
    also stores `locals`/`code` as raw functions (`Nat → Option _` /
    `FunName → Option _`) which admit infinite-support inhabitants, a strict
    superset of HOL's finite maps (`|->`). The statement quantifies the whole
    unrestricted state, so the `@[hol set_globals_def]` tag was withdrawn in the
    `flapjack-pxn.18.3.7.1.3.1.1.3` audit; exact finite-support carrier
    restoration is tracked by `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
def setCrepHolGlobalsW {width : Nat} [NeZero width] {σ : Type} (key : BitVec 5)
    (value : PanWordLab (BitVec width)) (state : CrepHolState (BitVec width) σ) :
    CrepHolState (BitVec width) σ :=
  { state with globals := FUPDATE state.globals (key, value) }

/-- Kernel-checked bridge: the width-indexed exact `set_globals` counterpart
    agrees with the generic production definition at `BitVec width`. -/
theorem setCrepHolGlobalsW_eq_setCrepHolGlobals {width : Nat} [NeZero width] {σ : Type}
    (key : BitVec 5) (value : PanWordLab (BitVec width))
    (state : CrepHolState (BitVec width) σ) :
    setCrepHolGlobalsW key value state = setCrepHolGlobals key value state := rfl

/-- Generic production clock decrement on the 11-field `CrepHolState`. HOL
    `crepSem$dec_clock_def` (`crepSemScript.sml:145-148`) is word-length indexed
    (`'a crepSem$state`), so this generic-`α` form is deliberately UNTAGGED; the
    width-indexed exact counterpart is `decCrepHolClockW` below. -/
def decCrepHolClock (state : CrepHolState α σ) : CrepHolState α σ :=
  { state with clock := state.clock - 1 }

/-! FLAPJACK-SPECIFIC (not a statement-exact HOL port). Source-reviewed against
    HOL `crepSem$dec_clock_def` (`cakeml/pancake/semantics/crepSemScript.sml:145-148`),
    which states `dec_clock s = s with clock := s.clock - 1`. The Lean clause
    matches that update (`{ state with clock := state.clock - 1 }`), and
    `[NeZero width]` excludes the invalid zero word dimension HOL's `'a word`
    also excludes. The mismatch is the quantified whole-state carrier: in
    `CrepHolState (BitVec width) σ` the fields `locals : Nat → Option _`,
    `globals : BitVec 5 → Option _` and `code : FunName → Option _`
    (CrepSem.lean:102-113) are raw functions that admit infinite-support
    inhabitants, a strict superset of HOL's finite maps `varname |-> 'a word_lab`,
    `5 word |-> 'a word_lab` and `funname |-> (varname list # prog)`
    (`crepSemScript.sml:20-31`), so the statement ranges over states HOL cannot
    represent. The `names_as_string` qualifier cannot authorize that carrier (the
    keys are not String-backed `mlstring` here) and no `NameRanged` byte witness
    applies because the result is a whole state, not a name. Direct HOL rows
    `dec_clock_clock=T`, `dec_clock_globals=T`, `dec_clock_be=T`,
    `dec_clock_top=T` are in `scripts/hol-probes/crep_dec_clock_simp_probe.out`,
    sampled by the bridge example in `Flapjack/Test/CrepGlobalShapeParity.lean:288-289`
    and used by `Flapjack/Test/CrepInlineRelParity.lean:434-435`. The
    `@[hol dec_clock_def]` tag was withdrawn in the
    `flapjack-pxn.18.3.7.1.3.1.1.3` audit and remains WITHDRAWN
    (`docs/HOL-THEOREM-MAP.json` records `decCrepHolClockW` as
    `documented_mismatch`); exact finite-support carrier restoration is tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.3.1` (the `CrepSemHOLState` finite-support carrier
    at `Flapjack/Pancake/Semantics/CrepSem/HOLState.lean` has no clock-update
    bridge yet). -/
def decCrepHolClockW {width : Nat} [NeZero width] {σ : Type} (state : CrepHolState (BitVec width) σ) :
    CrepHolState (BitVec width) σ :=
  { state with clock := state.clock - 1 }

/-- Kernel-checked bridge: the width-indexed exact `dec_clock` counterpart
    agrees with the generic production definition at `BitVec width`. -/
theorem decCrepHolClockW_eq_decCrepHolClock {width : Nat} [NeZero width] {σ : Type}
    (state : CrepHolState (BitVec width) σ) :
    decCrepHolClockW state = decCrepHolClock state := rfl

/-- Generic production local-binding update on the 11-field `CrepHolState`.
    HOL `crepSem$set_var_def` (`crepSemScript.sml:55-57`) is word-length indexed
    (`'a crepSem$state`), so this generic-`α` form is deliberately UNTAGGED; the
    width-indexed exact counterpart is `setCrepHolVarW` below. -/
def setCrepHolVar (name : Nat) (value : PanWordLab α)
    (state : CrepHolState α σ) : CrepHolState α σ :=
  { state with locals := FUPDATE state.locals (name, value) }

/-! FLAPJACK-SPECIFIC (not a statement-exact HOL port). Source-reviewed against
    HOL `crepSem$set_var_def` (`cakeml/pancake/semantics/crepSemScript.sml:55-57`),
    which states `set_var v w s = s with locals := s.locals |+ (v,w)`. The Lean
    clause matches that update: the `Nat` key is HOL's `varname = num`, the
    `PanWordLab (BitVec width)` value is the single-`Word` `word_lab` carrier at
    positive width, and `FUPDATE state.locals (name, value)` is the finite-map
    `|+` update. The mismatch is the quantified whole-state carrier: in
    `CrepHolState (BitVec width) σ` both `locals : Nat → Option _` and
    `code : FunName → Option _` are raw functions that admit infinite-support
    inhabitants, a strict superset of HOL's finite maps, so the statement ranges
    over states HOL's `num |-> 'a word_lab` cannot represent. The
    `names_as_string` qualifier cannot authorize that carrier (the key is not a
    String-backed `mlstring` here), and no `NameRanged` byte witness applies
    because the result is a whole state, not a name. Direct HOL rows are recorded
    in `scripts/hol-probes/crep_local_updates_probe.out`
    (`set_var_hit=T`, `set_var_keeps_other=T`, `set_var_fields_preserved=T`) and
    sampled by the `localBase` examples and `#guard` in
    `Flapjack/Test/CrepGlobalShapeParity.lean:227-269`. The `@[hol set_var_def]`
    tag was withdrawn in the `flapjack-pxn.18.3.7.1.3.1.1.3` audit and remains
    WITHDRAWN (`docs/HOL-THEOREM-MAP.json` records `setCrepHolVarW` as
    `documented_mismatch`); exact finite-support carrier restoration is tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
def setCrepHolVarW {width : Nat} [NeZero width] {σ : Type} (name : Nat)
    (value : PanWordLab (BitVec width)) (state : CrepHolState (BitVec width) σ) :
    CrepHolState (BitVec width) σ :=
  { state with locals := FUPDATE state.locals (name, value) }

/-- Kernel-checked bridge: the width-indexed exact `set_var` counterpart agrees
    with the generic production definition at `BitVec width`. -/
theorem setCrepHolVarW_eq_setCrepHolVar {width : Nat} [NeZero width] {σ : Type} (name : Nat)
    (value : PanWordLab (BitVec width)) (state : CrepHolState (BitVec width) σ) :
    setCrepHolVarW name value state = setCrepHolVar name value state := rfl

/-- Generic production callee-parameter update on the 11-field `CrepHolState`.
    HOL `crepSem$upd_locals_def` (`crepSemScript.sml:66-68`) is word-length
    indexed, so this generic-`α` form is deliberately UNTAGGED; the
    width-indexed exact counterpart is `updCrepHolLocalsW` below. -/
def updCrepHolLocals (varargs : List (Nat × PanWordLab α))
    (state : CrepHolState α σ) : CrepHolState α σ :=
  { state with locals := FUPDATE_LIST FEMPTY varargs }

/-! FLAPJACK-SPECIFIC (not a statement-exact HOL port): HOL
    `upd_locals_def` (`crepSemScript.sml:66-68`) sets `locals` to
    `FEMPTY |++ varargs`, preserving the other state fields. This definition
    matches that update clause, and `[NeZero width]` excludes invalid word
    dimensions, but its full state argument is `CrepHolState (BitVec width) σ`:
    `locals` and `code` are raw lookup functions with no finite-support
    witnesses, so this carrier includes states HOL's finite maps cannot
    represent. The direct rows `upd_locals_replace` and
    `locals_upd_locals_cells` pin update behavior only; they do not close this
    state-carrier gap. The source-shaped `CrepSemHOLState` now has finite
    support, and its `upd_locals` helper plus kernel-checked bridge to this
    executable state live in `CrepSem/HOLState.lean`
    (`CrepSemHOLState.updLocals`, `toBitVecEvaluatorState_updLocals`). The former
    is tagged over the reviewed positive-width `BitVec width` word carrier and
    finite-map translation; this broader raw-function variant remains untagged.
    The tag withdrawn by `flapjack-pxn.18.3.7.1.3.1.1.3` therefore remains
    withheld here. -/
def updCrepHolLocalsW {width : Nat} [NeZero width] {σ : Type}
    (varargs : List (Nat × PanWordLab (BitVec width)))
    (state : CrepHolState (BitVec width) σ) : CrepHolState (BitVec width) σ :=
  { state with locals := FUPDATE_LIST FEMPTY varargs }

/-- Kernel-checked bridge: the width-indexed exact `upd_locals` counterpart
    agrees with the generic production definition at `BitVec width`. -/
theorem updCrepHolLocalsW_eq_updCrepHolLocals {width : Nat} [NeZero width] {σ : Type}
    (varargs : List (Nat × PanWordLab (BitVec width)))
    (state : CrepHolState (BitVec width) σ) :
    updCrepHolLocalsW varargs state = updCrepHolLocals varargs state := rfl

/-- Generic production locals-clearing step on the 11-field `CrepHolState`.
    HOL `crepSem$empty_locals_def` (`crepSemScript.sml:71`) is word-length
    indexed, so this generic-`α` form is deliberately UNTAGGED; the
    width-indexed exact counterpart is `emptyCrepHolLocalsW` below. -/
def emptyCrepHolLocals (state : CrepHolState α σ) : CrepHolState α σ :=
  { state with locals := FEMPTY }

/-! FLAPJACK-SPECIFIC (not a statement-exact HOL port). Source-reviewed against
    HOL `crepSem$empty_locals_def` (`cakeml/pancake/semantics/crepSemScript.sml:71-74`),
    which states `empty_locals s = s with <| locals := FEMPTY |>` and leaves the
    other ten fields untouched. The Lean clause matches that update
    (`{ state with locals := FEMPTY }`), where the Lean `locals` is emptied
    pointwise. The mismatch is the quantified whole-state carrier: in
    `CrepHolState (BitVec width) σ` the fields `locals : Nat → Option _`,
    `globals : BitVec 5 → Option _` and `code : FunName → Option _`
    (CrepSem.lean:102-113) are raw functions that admit infinite-support
    inhabitants, a strict superset of HOL's finite maps `varname |-> 'a word_lab`,
    `5 word |-> 'a word_lab` and `funname |-> (varname list # prog)`
    (`crepSemScript.sml:20-31`), so the statement ranges over states HOL cannot
    represent. The `names_as_string` qualifier cannot authorize that carrier and
    no `NameRanged` byte witness applies because the result is a whole state, not
    a name. Direct HOL rows `empty_locals_locals=T`, `empty_locals_clock=T`,
    `empty_locals_memory=T` are in `scripts/hol-probes/crep_dec_clock_simp_probe.out`,
    and `empty_locals_none=T`, `empty_locals_fields_preserved=T` in
    `scripts/hol-probes/crep_local_updates_probe.out`; sampled by the bridge
    example in `Flapjack/Test/CrepGlobalShapeParity.lean:284-285`. The
    `@[hol empty_locals_def]` tag was withdrawn in the
    `flapjack-pxn.18.3.7.1.3.1.1.3` audit and remains WITHDRAWN
    (`docs/HOL-THEOREM-MAP.json` records `emptyCrepHolLocalsW` as
    `documented_mismatch`); exact finite-support carrier restoration is tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.3.1` (the `CrepSemHOLState` finite-support carrier
    at `Flapjack/Pancake/Semantics/CrepSem/HOLState.lean` has no locals-clearing
    bridge yet). -/
def emptyCrepHolLocalsW {width : Nat} [NeZero width] {σ : Type} (state : CrepHolState (BitVec width) σ) :
    CrepHolState (BitVec width) σ :=
  { state with locals := FEMPTY }

/-- Kernel-checked bridge: the width-indexed exact `empty_locals` counterpart
    agrees with the generic production definition at `BitVec width`. -/
theorem emptyCrepHolLocalsW_eq_emptyCrepHolLocals {width : Nat} [NeZero width] {σ : Type}
    (state : CrepHolState (BitVec width) σ) :
    emptyCrepHolLocalsW state = emptyCrepHolLocals state := rfl

/-- Generic production `res_var` on a key-generic finite map. HOL
    `crepSem$res_var_def` (`crepSemScript.sml:163`) is keyed by `num` with
    `'a word_lab` values and is word-length indexed, so the generic-`α` form is
    deliberately UNTAGGED; the width-indexed exact counterpart is `resVarW`
    below. `[LawfulBEq α]` ties the Boolean key equality used by the
    representation (`key == k`) to HOL's propositional equality. -/
def resVar [BEq α] [LawfulBEq α] (f : FiniteMap α β) (entry : α × Option β) : FiniteMap α β :=
  match entry.2 with
  | none => FDOMSUB f entry.1
  | some v => FUPDATE f (entry.1, v)

/-! FLAPJACK-SPECIFIC (not a statement-exact HOL port): the two clauses
    `res_var lc (n, NONE) = lc \\ n` and `res_var lc (n, SOME v) = lc |+ (n,v)`
    are HOL's (`crepSemScript.sml:163`), but the carrier is the raw function
    `FiniteMap Nat (PanWordLab (BitVec width))` (`= Nat → Option _`), which admits
    infinite-support inhabitants, a strict superset of HOL's `num |-> 'a word_lab`.
    The `@[hol res_var_def]` tag was withdrawn in the
    `flapjack-pxn.18.3.7.1.3.1.1.3` audit; an exact finite-support `res_var` and
    tag restoration are tracked by `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
def resVarW {width : Nat} [NeZero width] (f : FiniteMap Nat (PanWordLab (BitVec width)))
    (entry : Nat × Option (PanWordLab (BitVec width))) :
    FiniteMap Nat (PanWordLab (BitVec width)) :=
  resVar f entry

/-- Kernel-checked bridge: the width-indexed exact `res_var` counterpart agrees
    with the generic production definition at `Nat` keys / `BitVec width` values. -/
theorem resVarW_eq_resVar {width : Nat} [NeZero width] (f : FiniteMap Nat (PanWordLab (BitVec width)))
    (entry : Nat × Option (PanWordLab (BitVec width))) :
    resVarW f entry = resVar f entry := rfl

/-! ## FLAPJACK-SPECIFIC `=`-based `res_var` forms (NOT statement-exact HOL ports)

`crepSem$res_var_def` (`crepSemScript.sml:163`) is stated over HOL's finite
maps and HOL propositional equality.  The forms below use Lean `DecidableEq`
(the encoding of HOL `=`) and avoid the Boolean-`BEq` side conditions of the
executable `resVar`, but they still operate on the raw function carrier
`FiniteMap α β = α → Option β` (`Flapjack/FiniteMap/Basic.lean:19`), which
admits infinite-support inhabitants that HOL finite maps do not.  They are
therefore Flapjack-specific infrastructure, not statement-exact ports of the
`crepPropsProofScript.sml` / `crep_inlineProofScript.sml` `res_var` theorems:
the `@[hol]` tags for these forms were withdrawn and their manifest entries are
`documented_mismatch`.  The faithful replacement over the finite-support
`HolFiniteMapExact` carrier is tracked by `flapjack-pxn.18.3.7.1.3.1.1.3.1`.
The Boolean-`BEq` `resVar` above remains the executable implementation. -/

/-- HOL-equality form of `res_var`: delete the key on `none`, insert on `some`. -/
def resVarHOL [DecidableEq α] (f : FiniteMap α β) (entry : α × Option β) : FiniteMap α β :=
  match entry.2 with
  | none => FDOMSUB_HOL f entry.1
  | some v => FUPDATE_HOL f (entry.1, v)

/-- HOL-equality form of `flookup_res_var_thm`. -/
theorem FLOOKUP_resVarHOL [DecidableEq α] (f : FiniteMap α β) (m n : α) (v : Option β) :
    FLOOKUP (resVarHOL f (m, v)) n = if n = m then v else FLOOKUP f n := by
  cases v with
  | none => simp only [resVarHOL, FLOOKUP_FDOMSUB_HOL]
  | some w => simp only [resVarHOL, FLOOKUP_FUPDATE_HOL]

/-- HOL-equality form of `res_var_commutes`. -/
theorem resVarHOL_commutes [DecidableEq α] (lc lc' : FiniteMap α β) (n h : α)
    (hne : n ≠ h) :
    resVarHOL (resVarHOL lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
      resVarHOL (resVarHOL lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h) := by
  cases hh : FLOOKUP lc' h with
  | none =>
    cases hn : FLOOKUP lc' n with
    | none =>
      simp only [resVarHOL]
      rw [FDOMSUB_HOL_commutes lc h n hne.symm]
    | some vn =>
      simp only [resVarHOL]
      rw [FDOMSUB_HOL_FUPDATE_HOL_neq lc h n vn hne.symm]
  | some vh =>
    cases hn : FLOOKUP lc' n with
    | none =>
      simp only [resVarHOL]
      rw [FDOMSUB_HOL_FUPDATE_HOL_neq lc n h vh hne]
    | some vn =>
      simp only [resVarHOL]
      rw [FUPDATE_HOL_comm lc h vh n vn hne.symm]

/-- HOL-equality form of `flookup_res_var_distinct_eq`. -/
theorem FLOOKUP_foldl_resVarHOL_not_mem [DecidableEq α]
    (entries : List (α × Option β)) (f : FiniteMap α β) (x : α)
    (h : x ∉ entries.map Prod.fst) :
    FLOOKUP (entries.foldl resVarHOL f) x = FLOOKUP f x := by
  induction entries generalizing f with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, hrest⟩ := h
    rw [List.foldl_cons, ih (resVarHOL f entry) hrest, FLOOKUP_resVarHOL]
    simp [hne]

/-- HOL-equality form of `flookup_res_var_distinct_zip_eq`. -/
theorem FLOOKUP_foldl_resVarHOL_zip_not_mem [DecidableEq α]
    (xs : List α) (ys : List (Option β)) (f : FiniteMap α β) (x : α)
    (hlen : xs.length = ys.length) (h : x ∉ xs) :
    FLOOKUP ((xs.zip ys).foldl resVarHOL f) x = FLOOKUP f x := by
  apply FLOOKUP_foldl_resVarHOL_not_mem
  rw [List.map_fst_zip (by omega)]
  exact h

/-! HOL crep_op has exactly one operator constructor, Mul. This generic helper
is Flapjack production support; the exact word-typed HOL counterpart below is
specialized to every positive BitVec width. -/
/-- Generic production helper for Crep multiplication. This is intentionally
    untagged: HOL `crep_op_def` accepts `'a word`, whereas arbitrary `α` is not
    constrained to be a word carrier. -/
def crepOpCrep [Mul α] : CrepOp → List α → Option α
  | .mul, [left, right] => some (left * right)
  | _, _ => none

/-- Exact HOL-shaped port of `crepSem$crep_op_def` (crepSemScript.sml:85-88):
    `crep_op crepLang$Mul [w1;w2] = SOME (w1 * w2)` and `crep_op _ _ = NONE`.
    HOL's carrier is `'a word`, so the tagged port is width-polymorphic over
    `BitVec width` with the positive-width side condition `[NeZero width]`
    (HOL's `:'a word` requires a nonempty index type) rather than an arbitrary
    `[Mul α]`. The wildcard clause
    covers `.mul` at every other arity, matching HOL's total-over-malformed-
    operand-lists `crep_op _ _ = NONE`. The generic production evaluator still
    multiplies directly in its `.crepOp` clause; the RV64 executed-path
    instantiation is tested, but routing execution through this tagged
    definition remains open (bead flapjack-pxn.18.4.3.48.1.20). -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "crep_op_def"]
def crepOpCrepWord {width : Nat} [NeZero width] :
    CrepOp → List (BitVec width) → Option (BitVec width)
  | .mul, [left, right] => some (left * right)
  | _, _ => none

/-- The exact word-width port is definitionally the generic production helper
    when its carrier is a BitVec. -/
theorem crepOpCrepWord_eq_generic {width : Nat} [NeZero width]
    (operator : CrepOp) (arguments : List (BitVec width)) :
    crepOpCrepWord operator arguments = crepOpCrep operator arguments := by
  cases operator with
  | mul => cases arguments with
      | nil => rfl
      | cons left rest => cases rest with
          | nil => rfl
          | cons right tail => cases tail <;> rfl

/-- Compatibility name retained for existing target-adapter clients. -/
def crepOpValue [Mul α] : CrepOp → List α → Option α := crepOpCrep

/-- Compatibility equation for target-adapter clients of the generic operator. -/
@[simp] theorem crepOpValue_mul [Mul α] (left right : α) :
    crepOpValue .mul [left, right] = some (left * right) := by
  rfl

theorem crepOpCrep_eq_crepOpValue [Mul α] (operator : CrepOp)
    (arguments : List α) :
    crepOpCrep operator arguments = crepOpValue operator arguments := rfl

/-- Generic production memory load on the 11-field `CrepHolState`. HOL
    `crepSem$mem_load_def` (`crepSemScript.sml:48-52`) is word-length indexed,
    so the generic-`α` form is deliberately UNTAGGED; the width-indexed exact
    counterpart is `memLoadCrepHolW` below (also untagged: the whole-state
    carrier still admits infinite-support `locals`/`code`). -/
def memLoadCrepHol (address : α) (state : CrepHolState α σ) : Option (PanWordLab α) :=
  if state.memaddrs address then some (state.memory address) else none

/-! FLAPJACK-SPECIFIC (not a statement-exact HOL port): the clause
    `mem_load addr s = if addr IN s.memaddrs then SOME (s.memory addr) else NONE`
    is HOL's (`crepSemScript.sml:48-52`), and it reads only `memory : α →
    PanWordLab α` and `memaddrs : α → Bool`, but the carrier `CrepHolState
    (BitVec width) σ` also stores `locals`/`code` as raw functions (`Nat →
    Option _` / `FunName → Option _`) which admit infinite-support inhabitants,
    a strict superset of HOL's finite maps (`|->`). The statement quantifies the
    whole unrestricted state, so the `@[hol mem_load_def]` tag was withdrawn in
    the `flapjack-pxn.18.3.7.1.3.1.1.3` audit (same whole-state mismatch that
    forced the PanSem clock-only withdrawals); exact finite-support carrier
    restoration is tracked by `flapjack-pxn.18.3.7.1.3.1.1.3.1`. -/
def memLoadCrepHolW {width : Nat} [NeZero width] {σ : Type} (address : BitVec width)
    (state : CrepHolState (BitVec width) σ) : Option (PanWordLab (BitVec width)) :=
  if state.memaddrs address then some (state.memory address) else none

/-- Kernel-checked bridge: the width-indexed exact `mem_load` counterpart
    agrees with the generic production definition at `BitVec width`. -/
theorem memLoadCrepHolW_eq_memLoadCrepHol {width : Nat} [NeZero width] {σ : Type}
    (address : BitVec width) (state : CrepHolState (BitVec width) σ) :
    memLoadCrepHolW address state = memLoadCrepHol address state := rfl

/-- Forget the three target-configuration fields of the executable runtime
    state, obtaining the 11-field HOL-shaped state. -/
def CrepRuntimeState.toHolState (state : CrepRuntimeState α σ) :
    CrepHolState α σ :=
  { locals := state.locals
    globals := state.globals
    code := state.code
    memory := state.memory
    memaddrs := state.memaddrs
    shMemaddrs := state.shMemaddrs
    clock := state.clock
    bigEndian := state.bigEndian
    ffi := state.ffi
    baseAddress := state.baseAddress
    topAddress := state.topAddress }

/- Flapjack clock update. Its field operation follows CakeML Pancake's
   `dec_clock_def`, but this runtime state still carries extra memory-model
   and FFI-context fields, so this is not tagged as an exact HOL definition. -/
def decCrepClock (state : CrepRuntimeState α σ) : CrepRuntimeState α σ :=
  { state with clock := state.clock - 1 }

def updateCrepRuntimeGlobal (globals : BitVec 5 → Option (PanWordLab α))
    (key : BitVec 5) (value : PanWordLab α) : BitVec 5 → Option (PanWordLab α) :=
  fun candidate => if key == candidate then some value else globals candidate

/-- Production global update on the 14-field `CrepRuntimeState`. It derives its
    globals update by applying the tagged HOL `setCrepHolGlobals` to the
    11-field projection `CrepRuntimeState.toHolState` and writing the resulting
    globals back, so the three runtime configuration fields are preserved
    exactly as the record update leaves them. It is NOT itself tagged (HOL's
    state has 11 fields); `setCrepRuntimeGlobals_eq_FUPDATE` and
    `setCrepRuntimeGlobals_toHolState` are the kernel-checked adapters. -/
def setCrepRuntimeGlobals (key : BitVec 5) (value : PanWordLab α)
    (state : CrepRuntimeState α σ) : CrepRuntimeState α σ :=
  { state with
    globals := (setCrepHolGlobals key value state.toHolState).globals }

/-- The global-cell update is HOL's finite-map `|+`/`FUPDATE` on the
    function-represented globals map. -/
theorem updateCrepRuntimeGlobal_eq_FUPDATE
    (globals : BitVec 5 → Option (PanWordLab α)) (key : BitVec 5)
    (value : PanWordLab α) :
    updateCrepRuntimeGlobal globals key value = FUPDATE globals (key, value) := rfl

/-- `setCrepRuntimeGlobals` has exactly HOL's `set_globals_def` body once the
    globals cell update is written as the HOL finite-map update. -/
theorem setCrepRuntimeGlobals_eq_FUPDATE
    (key : BitVec 5) (value : PanWordLab α) (state : CrepRuntimeState α σ) :
    setCrepRuntimeGlobals key value state =
      { state with globals := FUPDATE state.globals (key, value) } := rfl

/-- Kernel-checked adapter: routing production StoreGlob through the tagged HOL
    definition only changes the globals component, leaving the 11 encoded
    fields equal to the HOL-shaped update. -/
theorem setCrepRuntimeGlobals_toHolState
    (key : BitVec 5) (value : PanWordLab α) (state : CrepRuntimeState α σ) :
    (setCrepRuntimeGlobals key value state).toHolState =
      setCrepHolGlobals key value state.toHolState := rfl

/-- Kernel-checked adapter: `toHolState` forgets exactly the three
    configuration fields, so it commutes with the production update. -/
theorem CrepRuntimeState.toHolState_globals (state : CrepRuntimeState α σ) :
    state.toHolState.globals = state.globals := rfl

def updateCrepRuntimeLocal (locals : Nat → Option (PanWordLab α))
    (name : Nat) (value : PanWordLab α) : Nat → Option (PanWordLab α) :=
  fun candidate => if name == candidate then some value else locals candidate

/-- The runtime local-cell update is HOL's finite-map `|+`/`FUPDATE` on the
    function-represented locals map, i.e. exactly the body of
    `crepSem$set_var_def` before the enclosing record write. -/
theorem updateCrepRuntimeLocal_eq_FUPDATE
    (locals : Nat → Option (PanWordLab α)) (name : Nat) (value : PanWordLab α) :
    updateCrepRuntimeLocal locals name value = FUPDATE locals (name, value) := rfl

/-- Production local-binding on the 14-field `CrepRuntimeState`, routed through
    the tagged HOL `setCrepHolVar` applied to the 11-field projection, so the
    three runtime configuration fields are preserved exactly as a record
    update leaves them. It is NOT itself tagged (HOL's state has 11 fields);
    `setCrepRuntimeLocal_eq_update` and `setCrepRuntimeLocal_toHolState` are
    the kernel-checked adapters. -/
def setCrepRuntimeLocal (name : Nat) (value : PanWordLab α)
    (state : CrepRuntimeState α σ) : CrepRuntimeState α σ :=
  { state with locals := (setCrepHolVar name value state.toHolState).locals }

/-- `setCrepRuntimeLocal` has HOL's `set_var` locals component. -/
@[simp] theorem setCrepRuntimeLocal_eq_update
    (name : Nat) (value : PanWordLab α) (state : CrepRuntimeState α σ) :
    setCrepRuntimeLocal name value state =
      { state with locals := updateCrepRuntimeLocal state.locals name value } := rfl

/-- Kernel-checked adapter: routing production locals through the tagged HOL
    `setCrepHolVar` leaves the 11 encoded fields equal to the HOL-shaped
    update. -/
theorem setCrepRuntimeLocal_toHolState
    (name : Nat) (value : PanWordLab α) (state : CrepRuntimeState α σ) :
    (setCrepRuntimeLocal name value state).toHolState =
      setCrepHolVar name value state.toHolState := rfl

/-- Flapjack update of the total HOL-shaped memory function. -/
def updateCrepRuntimeMemory [BEq α] (memory : α → PanWordLab α)
    (address : α) (value : PanWordLab α) : α → PanWordLab α :=
  fun candidate => if candidate == address then value else memory candidate

/- Flapjack local-clear operation. Its locals projection matches CakeML's
   `empty_locals_def` (`crepSemScript.sml:71`), but the enclosing state type
   still differs. Terminal timeout and exception boundaries do not expose
   the caller's transient locals. -/
def clearCrepRuntimeLocals (state : CrepRuntimeState α σ) : CrepRuntimeState α σ :=
  { state with locals := fun _ => none }

/-- Kernel-checked adapter: the production local-clear agrees with the tagged
    HOL `emptyCrepHolLocals` under the 11-field projection. -/
theorem clearCrepRuntimeLocals_toHolState (state : CrepRuntimeState α σ) :
    (clearCrepRuntimeLocals state).toHolState = emptyCrepHolLocals state.toHolState := rfl

/-- Flapjack-only projection lemma for the local-clear operation. -/
@[simp] theorem clearCrepRuntimeLocals_code (state : CrepRuntimeState α σ) :
    (clearCrepRuntimeLocals state).code = state.code := rfl

/-- `upd_locals` for callee parameters on the emitted `word_lab` cells: each
    bound value is wrapped with `PanWordLab.word`, exactly as HOL's cell type. -/
def assignCrepRuntimeLocals (locals : Nat → Option (PanWordLab α))
    (names : List Nat) (values : List α) :
    Option (Nat → Option (PanWordLab α)) :=
  if names.length != values.length then none
  else
    some ((names.zip values).foldl
      (fun locals (name, value) => updateCrepRuntimeLocal locals name (.word value))
      locals)

/-- Folding the runtime local-cell update over a list of `(name, value)` pairs
    is the HOL finite-map `|++`/`FUPDATE_LIST` over the same pairs with the raw
    values wrapped as `word_lab` cells. -/
theorem foldl_updateCrepRuntimeLocal_eq
    (entries : List (Nat × α)) (locals : Nat → Option (PanWordLab α)) :
    entries.foldl
        (fun acc entry => updateCrepRuntimeLocal acc entry.1 (.word entry.2))
        locals =
      (entries.map (fun entry => (entry.1, PanWordLab.word entry.2))).foldl
        FUPDATE locals := by
  induction entries generalizing locals with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [updateCrepRuntimeLocal_eq_FUPDATE, ih]

/-- Production `assignCrepRuntimeLocals` is exactly HOL's `|++` (`FUPDATE_LIST`)
    over the zipped `(name, word value)` bindings, with the same length guard. -/
theorem assignCrepRuntimeLocals_eq_FUPDATE_LIST
    (locals : Nat → Option (PanWordLab α)) (names : List Nat) (values : List α) :
    assignCrepRuntimeLocals locals names values =
      (if names.length != values.length then none
       else some (FUPDATE_LIST locals
         ((names.zip values).map (fun entry => (entry.1, PanWordLab.word entry.2))))) := by
  unfold assignCrepRuntimeLocals
  cases hb : names.length != values.length with
  | true => rfl
  | false =>
      rw [foldl_updateCrepRuntimeLocal_eq]
      rfl

/-- Production callee-local setup starts from the empty map (the `Call` clause),
    so it is HOL's `upd_locals` body `FEMPTY |++ varargs`. -/
theorem assignCrepRuntimeLocals_empty_eq
    (names : List Nat) (values : List α) (h : names.length = values.length) :
    assignCrepRuntimeLocals (fun _ => none) names values =
      some (FUPDATE_LIST FEMPTY
        ((names.zip values).map (fun entry => (entry.1, PanWordLab.word entry.2)))) := by
  rw [assignCrepRuntimeLocals_eq_FUPDATE_LIST]
  have hfalse : (names.length != values.length) = false := by
    cases hb : names.length != values.length with
    | false => rfl
    | true => exact (bne_iff_ne.mp hb h).elim
  rw [hfalse]
  rfl

/-- Kernel-checked adapter: writing the callee-locals map produced from the
    empty map into a runtime state projects to the tagged HOL `updCrepHolLocals`
    on the 11-field state. -/
theorem setCrepRuntimeLocalsFEMPTY_toHolState
    (varargs : List (Nat × PanWordLab α)) (state : CrepRuntimeState α σ) :
    ({ state with locals := FUPDATE_LIST FEMPTY varargs }).toHolState =
      updCrepHolLocals varargs state.toHolState := rfl

/-! ### `eraseDups`/`Nodup` bridge for routing the executed code lookup

    The executed lookup previously selected the duplicate-free check
    `parameters.eraseDups.length = parameters.length`; HOL `lookup_code_def`
    uses `ALL_DISTINCT` (`List.Nodup`).  The following Flapjack-specific lemmas
    (no HOL original) show these agree under `[LawfulBEq]`. -/

theorem filter_ne_eq_self_iff {α : Type} [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    l.filter (fun b => !(b == a)) = l ↔ a ∉ l := by
  rw [List.filter_eq_self]
  constructor
  · intro h ha
    have := h a ha
    simp at this
  · intro ha b hb
    have hne : (b == a) = false :=
      beq_eq_false_iff_ne.mpr (fun hba => ha (hba ▸ hb))
    simp [hne]

theorem eraseDups_sublist {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    List.Sublist l.eraseDups l :=
  (Nat.strongRecOn
    (motive := fun n => ∀ l : List α, l.length = n → List.Sublist l.eraseDups l)
    l.length (fun n ih l hl => by
      cases l with
      | nil => exact List.Sublist.slnil
      | cons a as =>
        rw [List.eraseDups_cons]
        have hfilt : List.Sublist (as.filter fun b => !(b == a)) as := List.filter_sublist
        have hlt : (as.filter fun b => !(b == a)).length < n := by
          have := hfilt.length_le
          simp only [List.length_cons] at hl
          omega
        exact List.Sublist.cons_cons a ((ih _ hlt _ rfl).trans hfilt)))
    l rfl

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup :=
  (Nat.strongRecOn
    (motive := fun n => ∀ l : List α, l.length = n → l.eraseDups.Nodup)
    l.length (fun n ih l hl => by
      cases l with
      | nil => exact List.nodup_nil
      | cons a as =>
        rw [List.eraseDups_cons, List.nodup_cons]
        have hfilt : List.Sublist (as.filter fun b => !(b == a)) as := List.filter_sublist
        have hlt : (as.filter fun b => !(b == a)).length < n := by
          have := hfilt.length_le
          simp only [List.length_cons] at hl
          omega
        refine ⟨?_, ih _ hlt _ rfl⟩
        intro hmem
        rw [List.mem_eraseDups, List.mem_filter] at hmem
        obtain ⟨_, hp⟩ := hmem
        simp at hp))
    l rfl

theorem eraseDups_eq_self_of_nodup_general {α : Type} [BEq α] [LawfulBEq α] (l : List α)
    (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.eraseDups_cons]
    obtain ⟨ha, has⟩ := List.nodup_cons.mp h
    have hf : as.filter (fun b => !(b == a)) = as := (filter_ne_eq_self_iff a as).mpr ha
    rw [hf, ih has]

theorem eraseDups_length_eq_iff_nodup {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.length = l.length ↔ l.Nodup := by
  constructor
  · intro h
    have heq : l.eraseDups = l := (eraseDups_sublist l).eq_of_length h
    rw [← heq]
    exact eraseDups_nodup l
  · intro hn
    rw [eraseDups_eq_self_of_nodup_general l hn]

/-- Flapjack's executable analogue of HOL `lookup_code_def`: look the function up, require the declared parameter
    list to have the argument count and be duplicate-free, and return the body
    together with the local finite map `FEMPTY |++ ZIP (ns,args)`.

    The HOL source quantifies `args : 'a word_lab list`; the executable
    `lookupCrepRuntimeCode` below consumes raw `List α` values and wraps them
    with `PanWordLab.word`. Its `len` argument is retained from the HOL
    `lookup_code` signature, where the definition does not inspect it.
    The generic-`α` form is deliberately UNTAGGED (HOL is word-length indexed);
    the width-indexed analogue is `lookupCrepHolCodeW` below. Neither declaration
    is tagged as a HOL port: HOL's `funname` and code-map key are `mlstring`
    (`crepSemScript.sml:17,23`), whereas `FunName` here is Lean `String`.
    The exact-key-carrier port remains open. -/
def lookupCrepHolCode (code : FunName → Option (List Nat × CrepProg α))
    (fname : FunName) (args : List (PanWordLab α)) (_len : Nat) :
    Option (CrepProg α × FiniteMap Nat (PanWordLab α)) :=
  match FLOOKUP code fname with
  | none => none
  | some (parameters, body) =>
      if parameters.length = args.length ∧ parameters.Nodup
      then some (body, FUPDATE_LIST FEMPTY (parameters.zip args))
      else none

/-- Width-indexed Flapjack analogue of `crepSem$lookup_code_def`
    (`crepSemScript.sml:76-84`) at the word-length carrier `BitVec width`: the
    code lookup must find a same-length duplicate-free parameter list, and
    returns the body with locals `FEMPTY |++ ZIP (parameters, args)`.  Defined
    as the width-specialized production `lookupCrepHolCode`, so the bridge below
    is definitional. This is not a HOL port: its `FunName = String` code-map key
    differs from HOL's `funname = mlstring`. -/
def lookupCrepHolCodeW {width : Nat} [NeZero width]
    (code : FunName → Option (List Nat × CrepProg (BitVec width)))
    (fname : FunName) (args : List (PanWordLab (BitVec width))) (len : Nat) :
    Option (CrepProg (BitVec width) × FiniteMap Nat (PanWordLab (BitVec width))) :=
  lookupCrepHolCode code fname args len

/-- Kernel-checked bridge: the width-indexed Flapjack `lookup_code` analogue
    agrees with the generic production definition at `BitVec width`. -/
theorem lookupCrepHolCodeW_eq_lookupCrepHolCode {width : Nat} [NeZero width]
    (code : FunName → Option (List Nat × CrepProg (BitVec width)))
    (fname : FunName) (args : List (PanWordLab (BitVec width))) (len : Nat) :
    lookupCrepHolCodeW code fname args len = lookupCrepHolCode code fname args len :=
  rfl

/-- Executed code lookup routed literally through the Flapjack
    `lookupCrepHolCode` definition: the runtime passes evaluated words as
    `PanWordLab.word` cells and reuses the same finite-map local representation.
    The word-width-specific counterpart `lookupCrepHolCodeW` is
    definitionally equal to this helper. -/
def lookupCrepRuntimeCode [BEq String] (name : FunName) (values : List α)
    (code : FunName → Option (List Nat × CrepProg α)) :
    Option (CrepProg α × (Nat → Option (PanWordLab α))) :=
  lookupCrepHolCode code name (values.map PanWordLab.word) 0

theorem zip_word_eq {α : Type} (names : List Nat) (values : List α) :
    names.zip (values.map PanWordLab.word) =
      (names.zip values).map (fun entry => (entry.1, PanWordLab.word entry.2)) := by
  rw [List.zip_map_right]
  rfl

/-- Definitional bridge: the executed lookup routes literally through the
    tagged HOL-shaped `lookupCrepHolCode` on the wrapped arguments, so the two
    sides are identical (the `len` argument is unused by the definition). -/
theorem lookupCrepRuntimeCode_eq_lookupCrepHolCode [BEq String] [LawfulBEq String]
    (name : FunName) (values : List α) (len : Nat)
    (code : FunName → Option (List Nat × CrepProg α)) :
    lookupCrepRuntimeCode name values code =
    lookupCrepHolCode code name (values.map PanWordLab.word) len := by
  rfl

/-- The production call adapter is the positive-width specialization of the
    untagged Flapjack `lookup_code` analogue. Runtime arguments are wrapped as HOL
    `word_lab` words; the returned body and finite-map locals retain exactly
    the source result representation. This bridge adds no call-success premise
    and does not depend on arithmetic simplification correctness. It is a
    Flapjack-specific adapter lemma with no separate HOL declaration. The
    `mlstring` code-key mismatch described above still applies. -/
theorem lookupCrepRuntimeCode_eq_lookupCrepHolCodeW {width : Nat}
    [NeZero width] [BEq String]
    (name : FunName) (values : List (BitVec width)) (len : Nat)
    (code : FunName → Option (List Nat × CrepProg (BitVec width))) :
    lookupCrepRuntimeCode name values code =
      lookupCrepHolCodeW code name (values.map PanWordLab.word) len := by
  rfl

inductive CrepRuntimeRequest (α : Type u) where
  | extCall (function : FunName)
      (configuration array : List UInt8)
  | sharedMem (operator : CrepMemOp) (name : Nat) (address : α)
      (payload : List UInt8)
  deriving DecidableEq, Repr

inductive CrepRuntimeFfiResponse (σ ε : Type u) where
  | returned (ffi : FfiState σ) (bytes : List UInt8)
  | final (event : ε)

abbrev CrepRuntimeFfiHandler (α σ ε : Type u) :=
  CrepRuntimeRequest α → FfiState σ → CrepRuntimeFfiResponse σ ε

inductive CrepRuntimeResult (α ε : Type u) where
  | normal
  | error
  | timeout
  | broke (label : Nat)
  | continued (label : Nat)
  | returned (values : List α)
  | raised (exception : α)
  | finalFfi (event : ε)
  deriving DecidableEq, Repr

/-- Exact constructor-by-constructor encoding of HOL's `crepSem$result`
    (`crepSemScript.sml:37-44`): `Error | TimeOut | Break num | Continue num |
    Return (('a word_lab) list) | Exception ('a word) | FinalFFI final_event`.
    Unlike `CrepRuntimeResult` it has no Flapjack-only `normal` convenience
    constructor, so it is the exact carrier for ports of proof-script
    definitions stated over `crepSem$result` such as `cont_res_def`. -/
inductive CrepResultHOL (α ε : Type u) where
  | error
  | timeOut
  | break (label : Nat)
  | continue (label : Nat)
  | return (values : List (PanWordLab α))
  | exception (value : α)
  | finalFfi (event : ε)
  deriving DecidableEq, Repr

abbrev CrepRuntimeStep (α σ ε : Type u) :=
  CrepRuntimeResult α ε × CrepRuntimeState α σ

/-- Generic production clock-clamping on the 11-field `CrepHolState`. HOL
    `crepSem$fix_clock_def` (`crepSemScript.sml:150-152`) is word-length indexed
    (`'a crepSem$state`), so this generic-`α` form is deliberately UNTAGGED; the
    width-indexed exact counterpart is `fixCrepHolClockW` below. -/
def fixCrepHolClock (oldState : CrepHolState α σ)
    (step : CrepRuntimeResult α ε × CrepHolState α σ) :
    CrepRuntimeResult α ε × CrepHolState α σ :=
  (step.1,
    { step.2 with
      clock :=
        if oldState.clock < step.2.clock then oldState.clock else step.2.clock })

/-! FLAPJACK-SPECIFIC (not a statement-exact HOL port). Source-reviewed against
    HOL `crepSem$fix_clock_def` (`cakeml/pancake/semantics/crepSemScript.sml:150-152`),
    which states `fix_clock old_s (res, new_s) = (res, new_s with clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock)`;
    the Lean clamp is clause-for-clause identical, with the HOL result/state pair
    exposed as the `β × CrepHolState ...` binder `step`. The mismatch is the
    quantified whole-state carrier: in `CrepHolState (BitVec width) σ` the fields
    `locals : Nat → Option _`, `globals : BitVec 5 → Option _` and
    `code : FunName → Option _` (CrepSem.lean:102-113) are raw functions that admit
    infinite-support inhabitants, a strict superset of HOL's finite maps
    `varname |-> 'a word_lab`, `5 word |-> 'a word_lab` and
    `funname |-> (varname list # prog)` (`crepSemScript.sml:20-31`), so the
    statement ranges over states HOL cannot represent. The `names_as_string`
    qualifier cannot authorize that carrier and no `NameRanged` byte witness
    applies because the result is a state, not a name. Direct HOL rows
    `fix_clock_clamps=(...)` and `fix_clock_keeps_lower=(...)` are in
    `scripts/hol-probes/crep_fix_clock_probe.out`; the clamp is sampled by
    `Flapjack/Test/CrepGlobalShapeParity.lean:292-296`. The `@[hol fix_clock_def]`
    tag was withdrawn in the `flapjack-pxn.18.3.7.1.3.1.1.3` audit and remains
    WITHDRAWN (`docs/HOL-THEOREM-MAP.json` records `fixCrepHolClockW` as
    `documented_mismatch`); exact finite-support carrier restoration is tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.3.1` (the `CrepSemHOLState` finite-support carrier
    at `Flapjack/Pancake/Semantics/CrepSem/HOLState.lean` now has the `set_var`/
    `set_globals`/`upd_locals`/`empty_locals`/`res_var` helpers but still no
    `fix_clock` bridge). -/
def fixCrepHolClockW {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (oldState : CrepHolState (BitVec width) σ)
    (step : β × CrepHolState (BitVec width) σ) :
    β × CrepHolState (BitVec width) σ :=
  (step.1,
    { step.2 with
      clock :=
        if oldState.clock < step.2.clock then oldState.clock else step.2.clock })

/-- Kernel-checked bridge: the width-indexed exact `fix_clock` counterpart
    agrees with the generic production definition at `BitVec width` for the
    production `CrepRuntimeResult` carrier. -/
theorem fixCrepHolClockW_eq_fixCrepHolClock {width : Nat} [NeZero width] {σ ε : Type}
    (oldState : CrepHolState (BitVec width) σ)
    (step : CrepRuntimeResult (BitVec width) ε × CrepHolState (BitVec width) σ) :
    fixCrepHolClockW oldState step = fixCrepHolClock oldState step := rfl

/-- The clock bound `fix_clock_IMP_LESS_EQ` (crepSemScript.sml:155-157): the
    clamped clock never exceeds the old state's clock.  Untagged here because
    the Lean statement takes the argument pair apart with explicit `result` /
    `newState` binders, whereas HOL destructures the pair in the hypothesis. -/
theorem fixCrepHolClock_clock_le (oldState : CrepHolState α σ)
    (result : CrepRuntimeResult α ε) (newState : CrepHolState α σ) :
    (fixCrepHolClock oldState (result, newState)).2.clock ≤ oldState.clock := by
  by_cases hlt : oldState.clock < newState.clock
  · simp [fixCrepHolClock, hlt]
  · simp only [fixCrepHolClock, hlt, if_false]
    exact Nat.le_of_not_lt hlt

/-- Generic production clock bound for the generic (untagged)
    `fixCrepHolClock`. HOL `fix_clock_IMP_LESS_EQ` (`crepSemScript.sml:155-157`)
    is word-length indexed (`'a crepSem$state`) and result-polymorphic, so this
    generic-`α` form is deliberately UNTAGGED; the width-indexed exact
    counterpart is `fixCrepHolClock_IMP_LESS_EQW` below. -/
theorem fixCrepHolClock_IMP_LESS_EQ (oldState : CrepHolState α σ)
    (step : CrepRuntimeResult α ε × CrepHolState α σ)
    (result : CrepRuntimeResult α ε) (newState : CrepHolState α σ)
    (hfixed : fixCrepHolClock oldState step = (result, newState)) :
    newState.clock ≤ oldState.clock := by
  obtain ⟨stepResult, stepState⟩ := step
  have hbound := fixCrepHolClock_clock_le oldState stepResult stepState
  rw [hfixed] at hbound
  exact hbound

/-! FLAPJACK-SPECIFIC (not a statement-exact HOL port). Source-reviewed against
    HOL `crepSem$fix_clock_IMP_LESS_EQ` (`cakeml/pancake/semantics/crepSemScript.sml:155-160`),
    which states `!x. fix_clock s x = (res,s1) ==> s1.clock <= s.clock`. The Lean
    bound is the same inequality, with the HOL pair variable `x` and the implicit
    `res`/`s1` exposed as the explicit binders `step`/`result`/`newState` (an
    inessential binder reshaping, not a semantic difference). The mismatch is the
    quantified whole-state carrier: in `CrepHolState (BitVec width) σ` the fields
    `locals : Nat → Option _`, `globals : BitVec 5 → Option _` and
    `code : FunName → Option _` (CrepSem.lean:102-113) are raw functions that admit
    infinite-support inhabitants, a strict superset of HOL's finite maps
    `varname |-> 'a word_lab`, `5 word |-> 'a word_lab` and
    `funname |-> (varname list # prog)` (`crepSemScript.sml:20-31`), so the
    statement ranges over states HOL cannot represent. The `names_as_string`
    qualifier cannot authorize that carrier and no `NameRanged` byte witness
    applies because the result is an inequality on a state field, not a name.
    Direct HOL rows `fix_clock_clamps=(...)` and `fix_clock_keeps_lower=(...)` are
    in `scripts/hol-probes/crep_fix_clock_probe.out`; the bound is sampled by
    `Flapjack/Test/CrepGlobalShapeParity.lean:307-312`. The
    `@[hol fix_clock_IMP_LESS_EQ]` tag was withdrawn in the
    `flapjack-pxn.18.3.7.1.3.1.1.3` audit and remains WITHDRAWN
    (`docs/HOL-THEOREM-MAP.json` records `fixCrepHolClock_IMP_LESS_EQW` as
    `documented_mismatch`); exact finite-support carrier restoration is tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.3.1` (the `CrepSemHOLState` finite-support carrier
    at `Flapjack/Pancake/Semantics/CrepSem/HOLState.lean` has no `fix_clock`
    bridge yet). -/
theorem fixCrepHolClock_IMP_LESS_EQW {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (oldState : CrepHolState (BitVec width) σ)
    (step : β × CrepHolState (BitVec width) σ)
    (result : β) (newState : CrepHolState (BitVec width) σ)
    (hfixed : fixCrepHolClockW oldState step = (result, newState)) :
    newState.clock ≤ oldState.clock := by
  obtain ⟨stepResult, stepState⟩ := step
  have hbound :
      (fixCrepHolClockW oldState (stepResult, stepState)).2.clock ≤
        oldState.clock := by
    by_cases hlt : oldState.clock < stepState.clock
    · simp [fixCrepHolClockW, hlt]
    · simp only [fixCrepHolClockW, hlt, if_false]
      exact Nat.le_of_not_lt hlt
  rw [hfixed] at hbound
  exact hbound

def crepRuntimeMemWidth : CrepMemOp → Nat
  | .load | .store => 0
  | .load8 | .store8 => 1
  | .load16 | .store16 => 2
  | .load32 | .store32 => 4

def crepRuntimeSharedAddress (state : CrepRuntimeState α σ)
    (operator : CrepMemOp) (address : α) : α :=
  if crepRuntimeMemWidth operator = 0 then address
  else state.memoryModel.byteAlign state.bytesInWord address

def crepRuntimeSharedAddressValid (state : CrepRuntimeState α σ)
    (operator : CrepMemOp) (address : α) : Bool :=
  state.shMemaddrs (crepRuntimeSharedAddress state operator address)

def crepRuntimeLoad (state : CrepRuntimeState α σ) (address : α) : Option α :=
  if state.memaddrs address then some (panTheWord (state.memory address)) else none

/-- The executed runtime word load is the tagged HOL `mem_load` on the
    `toHolState` view, with the `word_lab` cell projected by `panTheWord`. -/
theorem crepRuntimeLoad_eq_memLoadCrepHol (state : CrepRuntimeState α σ) (address : α) :
    crepRuntimeLoad state address =
      (memLoadCrepHol address state.toHolState).map panTheWord := by
  by_cases h : state.memaddrs address <;>
    simp [crepRuntimeLoad, memLoadCrepHol, CrepRuntimeState.toHolState, h]

def crepRuntimeLoadByte [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) : Option α :=
  let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
  if state.memaddrs alignedAddress then
    pure (state.memoryModel.getByte state.bytesInWord address
      (panTheWord (state.memory alignedAddress)) state.bigEndian)
  else none

def crepRuntimeLoad32 [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) : Option α :=
  if state.memoryModel.aligned 4 address then
    let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
    if state.memaddrs alignedAddress then
      let value := panTheWord (state.memory alignedAddress)
      pure (state.memoryModel.wordOfBytes32 state.bigEndian
        [state.memoryModel.getByte state.bytesInWord address value state.bigEndian,
         state.memoryModel.getByte state.bytesInWord (address + 1) value state.bigEndian,
         state.memoryModel.getByte state.bytesInWord (address + 1 + 1) value state.bigEndian,
         state.memoryModel.getByte state.bytesInWord (address + 1 + 1 + 1)
           value state.bigEndian])
    else none
  else none

def crepRuntimeStore [BEq α] (state : CrepRuntimeState α σ)
    (address value : α) : Option (CrepRuntimeState α σ) :=
  if state.memaddrs address then
    some { state with memory := updateCrepRuntimeMemory state.memory address (.word value) }
  else none

def crepRuntimeStoreByte [BEq α] [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    Option (CrepRuntimeState α σ) :=
  let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
  if state.memaddrs alignedAddress then
    let cell := panTheWord (state.memory alignedAddress)
    let updated := state.memoryModel.setByte state.bytesInWord address value cell state.bigEndian
    pure { state with memory := updateCrepRuntimeMemory state.memory alignedAddress (.word updated) }
  else none

def crepRuntimeStore32 [BEq α] [Add α] [OfNat α 0] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    Option (CrepRuntimeState α σ) :=
  if state.memoryModel.aligned 4 address then
    let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
    if state.memaddrs alignedAddress then
      let cell := panTheWord (state.memory alignedAddress)
      let cell0 := state.memoryModel.setByte state.bytesInWord address
        (state.memoryModel.getByte state.bytesInWord 0 value state.bigEndian)
        cell state.bigEndian
      let cell1 := state.memoryModel.setByte state.bytesInWord (address + 1)
        (state.memoryModel.getByte state.bytesInWord 1 value state.bigEndian)
        cell0 state.bigEndian
      let cell2 := state.memoryModel.setByte state.bytesInWord (address + 1 + 1)
        (state.memoryModel.getByte state.bytesInWord (1 + 1) value state.bigEndian)
        cell1 state.bigEndian
      let cell3 := state.memoryModel.setByte state.bytesInWord (address + 1 + 1 + 1)
        (state.memoryModel.getByte state.bytesInWord (1 + 1 + 1) value state.bigEndian)
        cell2 state.bigEndian
      pure { state with memory := updateCrepRuntimeMemory state.memory alignedAddress (.word cell3) }
    else none
  else none

/-- Flapjack-only view of the total HOL-shaped memory as an `Option`-valued
    function (`some` of the carried word). This reconciles the production total
    `word_lab` memory with the `Option`-valued RISC-V pan memory model; the
    `word_lab` cell has a single constructor, so no cell is dropped. -/
def crepRuntimeMemoryView (memory : α → PanWordLab α) : α → Option α :=
  fun address => some (panTheWord (memory address))

theorem crepRuntimeMemoryView_updateCrepRuntimeMemory_word [BEq α]
    (memory : α → PanWordLab α) (address : α) (value : α) :
    crepRuntimeMemoryView (updateCrepRuntimeMemory memory address (.word value)) =
      updateMemory (crepRuntimeMemoryView memory) address value := by
  funext current
  by_cases hsame : current == address <;>
    simp [crepRuntimeMemoryView, updateCrepRuntimeMemory, updateMemory, panTheWord, hsame]

/-- Flapjack-only: memory-level view of a production word store. -/
theorem crepRuntimeStore_eq_memory_view [BEq α]
    (state : CrepRuntimeState α σ) (address value : α) :
    (crepRuntimeStore state address value).map (fun s => crepRuntimeMemoryView s.memory) =
      if state.memaddrs address then
        some (updateMemory (crepRuntimeMemoryView state.memory) address value) else none := by
  rw [crepRuntimeStore]
  by_cases h : state.memaddrs address = true
  · rw [if_pos h, if_pos h]
    simp only [Option.map_some]
    exact congrArg some
      (crepRuntimeMemoryView_updateCrepRuntimeMemory_word state.memory address value)
  · rw [if_neg h, if_neg h]
    rfl

/-- Flapjack-only: memory-level view of a production byte store. -/
theorem crepRuntimeStoreByte_eq_memory_view [BEq α] [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    (crepRuntimeStoreByte state address value).map (fun s => crepRuntimeMemoryView s.memory) =
      if state.memaddrs (state.memoryModel.byteAlign state.bytesInWord address) then
        some (updateMemory (crepRuntimeMemoryView state.memory)
          (state.memoryModel.byteAlign state.bytesInWord address)
          (state.memoryModel.setByte state.bytesInWord address value
            (panTheWord (state.memory (state.memoryModel.byteAlign state.bytesInWord address)))
            state.bigEndian)) else none := by
  simp only [crepRuntimeStoreByte]
  by_cases h : state.memaddrs (state.memoryModel.byteAlign state.bytesInWord address) = true
  · rw [if_pos h, if_pos h]
    simp only [Option.pure_def, Option.map_some]
    exact congrArg some
      (crepRuntimeMemoryView_updateCrepRuntimeMemory_word state.memory _ _)
  · rw [if_neg h, if_neg h]
    rfl

/-- Flapjack-only: memory-level view of a production 32-bit store. -/
theorem crepRuntimeStore32_eq_memory_view [BEq α] [Add α] [OfNat α 0] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    (crepRuntimeStore32 state address value).map (fun s => crepRuntimeMemoryView s.memory) =
      if state.memoryModel.aligned 4 address then
        (if state.memaddrs (state.memoryModel.byteAlign state.bytesInWord address) then
          some (updateMemory (crepRuntimeMemoryView state.memory)
            (state.memoryModel.byteAlign state.bytesInWord address)
            (state.memoryModel.setByte state.bytesInWord (address + 1 + 1 + 1)
              (state.memoryModel.getByte state.bytesInWord (1 + 1 + 1) value state.bigEndian)
              (state.memoryModel.setByte state.bytesInWord (address + 1 + 1)
                (state.memoryModel.getByte state.bytesInWord (1 + 1) value state.bigEndian)
                (state.memoryModel.setByte state.bytesInWord (address + 1)
                  (state.memoryModel.getByte state.bytesInWord 1 value state.bigEndian)
                  (state.memoryModel.setByte state.bytesInWord address
                    (state.memoryModel.getByte state.bytesInWord 0 value state.bigEndian)
                    (panTheWord (state.memory (state.memoryModel.byteAlign state.bytesInWord address)))
                    state.bigEndian) state.bigEndian) state.bigEndian) state.bigEndian))
        else none)
      else none := by
  simp only [crepRuntimeStore32]
  by_cases ha : state.memoryModel.aligned 4 address = true
  · rw [if_pos ha, if_pos ha]
    by_cases hb : state.memaddrs (state.memoryModel.byteAlign state.bytesInWord address) = true
    · rw [if_pos hb, if_pos hb]
      simp only [Option.pure_def, Option.map_some]
      exact congrArg some
        (crepRuntimeMemoryView_updateCrepRuntimeMemory_word state.memory _ _)
    · rw [if_neg hb, if_neg hb]
      rfl
  · rw [if_neg ha, if_neg ha]
    rfl

/-- Flapjack-only: the single-constructor `word_lab` cell is recovered by
    re-wrapping its carried word. -/
theorem panWordLab_word_panTheWord (cell : PanWordLab α) :
    PanWordLab.word (panTheWord cell) = cell := by
  cases cell
  rfl

/-- Flapjack-only: re-totalize an `Option`-valued view into the production total
    memory, using `fallback` for cells the view does not carry. Since the
    production cell has a single constructor, a view that came from a total
    memory round-trips exactly. -/
def crepRuntimeMemoryOfView (view : α → Option α)
    (fallback : α → PanWordLab α) : α → PanWordLab α :=
  fun address => match view address with
    | some value => .word value
    | none => fallback address

theorem crepRuntimeMemoryOfView_view (memory : α → PanWordLab α) :
    crepRuntimeMemoryOfView (crepRuntimeMemoryView memory) memory = memory := by
  funext address
  simp only [crepRuntimeMemoryView, crepRuntimeMemoryOfView]
  rw [panWordLab_word_panTheWord]

theorem crepRuntimeMemoryOfView_updateMemory_word [BEq α]
    (memory : α → PanWordLab α) (address value : α) :
    crepRuntimeMemoryOfView
        (updateMemory (crepRuntimeMemoryView memory) address value) memory =
      updateCrepRuntimeMemory memory address (.word value) := by
  funext current
  by_cases hsame : current == address
  · simp [crepRuntimeMemoryOfView, updateMemory, updateCrepRuntimeMemory, hsame]
  · simp [crepRuntimeMemoryOfView, updateMemory, updateCrepRuntimeMemory,
      crepRuntimeMemoryView, hsame, panWordLab_word_panTheWord]

/-- Locals-level reference fold for assigning call return values onto existing
    word variables (HOL `upd_locals`/`FUPDATE_LIST` over existing names). Kept
    as the proof-side counterpart of `setCrepRuntimeLocalsExisting`, which is
    what the executed `crepRuntimeCall` paths use. -/
def crepRuntimeAssignExisting
    (locals : Nat → Option (PanWordLab α)) (names : List Nat) (values : List α) :
    Option (Nat → Option (PanWordLab α)) :=
  if names.length != values.length then none
  else if !names.all (fun name => (locals name).isSome) then none
  else if names.eraseDups.length != names.length then none
  else
    some ((names.zip values).foldl
      (fun locals (name, value) => updateCrepRuntimeLocal locals name (.word value))
      locals)

/-- State-level `crepRuntimeAssignExisting` whose fold routes through the tagged
    HOL `set_var` definition via `setCrepRuntimeLocal`. This is the helper used
    by the executed `crepRuntimeCall` returned-with-destinations path. -/
def setCrepRuntimeLocalsExisting (names : List Nat) (values : List α)
    (state : CrepRuntimeState α σ) : Option (CrepRuntimeState α σ) :=
  if names.length != values.length then none
  else if !names.all (fun name => (state.locals name).isSome) then none
  else if names.eraseDups.length != names.length then none
  else
    some ((names.zip values).foldl
      (fun state pair => setCrepRuntimeLocal pair.1 (.word pair.2) state) state)

theorem foldl_setCrepRuntimeLocal_eq (entries : List (Nat × α))
    (state : CrepRuntimeState α σ) :
    entries.foldl (fun state pair => setCrepRuntimeLocal pair.1 (.word pair.2) state)
        state =
      { state with
        locals :=
          entries.foldl
            (fun locals pair => updateCrepRuntimeLocal locals pair.1 (.word pair.2))
            state.locals } := by
  induction entries generalizing state with
  | nil => rfl
  | cons pair rest ih =>
      simp only [List.foldl_cons]
      rw [setCrepRuntimeLocal_eq_update, ih]

@[simp] theorem setCrepRuntimeLocalsExisting_eq (names : List Nat) (values : List α)
    (state : CrepRuntimeState α σ) :
    setCrepRuntimeLocalsExisting names values state =
      (crepRuntimeAssignExisting state.locals names values).map
        (fun locals => { state with locals := locals }) := by
  unfold setCrepRuntimeLocalsExisting crepRuntimeAssignExisting
  cases hlen : names.length != values.length with
  | true => rfl
  | false =>
      cases hall : !names.all (fun name => (state.locals name).isSome) with
      | true => rfl
      | false =>
          cases hdup : names.eraseDups.length != names.length with
          | true => rfl
          | false =>
              rw [foldl_setCrepRuntimeLocal_eq]
              rfl

def crepRuntimeReadBytes [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) : Nat → Option (List UInt8)
  | 0 => some []
  | length + 1 => do
      let value ← crepRuntimeLoadByte state address
      let rest ← crepRuntimeReadBytes state (address + 1) length
      pure (state.ffiContext.wordToByte value :: rest)
termination_by length => length

def crepRuntimeWriteBytes [BEq α] [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) :
    List UInt8 → Option (CrepRuntimeState α σ)
  | [] => some state
  | byte :: bytes => do
      let tailState ← crepRuntimeWriteBytes state (address + 1) bytes
      match crepRuntimeStoreByte tailState address
          (state.ffiContext.byteToWord byte) with
      | some updatedState => some updatedState
      | none => some state
termination_by bytes => sizeOf bytes

def crepRuntimeExtCallValues [BEq α] [Add α] [OfNat α 1]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : α) :
    CrepRuntimeStep α σ ε :=
  match crepRuntimeReadBytes state configuration
      (state.ffiContext.valueToNat configurationLength),
      crepRuntimeReadBytes state array
        (state.ffiContext.valueToNat arrayLength) with
  | some configurationBytes, some arrayBytes =>
      match handler (.extCall function configurationBytes arrayBytes) state.ffi with
      | .returned ffi bytes =>
          let state := { state with ffi := ffi }
          match crepRuntimeWriteBytes state array bytes with
          | some state => (.normal, state)
          | none => (.error, state)
      | .final event => (.finalFfi event, state)
  | _, _ => (.error, state)

def crepRuntimeExtCall [BEq α] [Add α] [OfNat α 1]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    CrepRuntimeStep α σ ε :=
  match (state.locals configuration).map panTheWord,
      (state.locals configurationLength).map panTheWord,
      (state.locals array).map panTheWord,
      (state.locals arrayLength).map panTheWord with
  | some configuration, some configurationLength, some array, some arrayLength =>
      crepRuntimeExtCallValues handler state function configuration configurationLength
        array arrayLength
  | _, _, _, _ => (.error, state)

def crepRuntimeSharedMem (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) : CrepRuntimeStep α σ ε :=
  if crepRuntimeSharedAddressValid state operator address then
    match operator with
    | .load | .load8 | .load16 | .load32 =>
        let payload := state.ffiContext.wordToBytes address false
        match handler (.sharedMem operator name address payload) state.ffi with
        | .returned ffi bytes =>
            let value := state.ffiContext.wordOfBytes false bytes
            let state := { state with ffi := ffi }
            (.normal, setCrepRuntimeLocal name (.word value) state)
        | .final event => (.finalFfi event, clearCrepRuntimeLocals state)
    | .store | .store8 | .store16 | .store32 =>
        match (state.locals name).map panTheWord with
        | none => (.error, state)
        | some value =>
            let width := crepRuntimeMemWidth operator
            let valueBytes := state.ffiContext.wordToBytes value false
            let addressBytes := state.ffiContext.wordToBytes address false
            let payload :=
              if width = 0 then valueBytes ++ addressBytes
              else valueBytes.take width ++ addressBytes
            match handler (.sharedMem operator name address payload) state.ffi with
            | .returned ffi _ => (.normal, { state with ffi := ffi })
            | .final event => (.finalFfi event, state)
  else
    (.error, state)

def evalCrepRuntimeExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : CrepExp α → Option α
  | .const value => some value
  | .var name => (state.locals name).map panTheWord
  | .load address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoad state address
  | .load32 address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoad32 state address
  | .loadByte address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoadByte state address
  | .loadGlob address => (state.globals address).map panTheWord
  | .op operator expressions => do
      let values ← expressions.mapM (evalCrepRuntimeExp state)
      state.memoryModel.wordOp operator values
  | .crepOp .mul [left, right] => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      crepOpCrep .mul [left, right]
  | .cmp operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (state.memoryModel.compare operator left right)
  | .shift operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      state.memoryModel.shift operator left right
  | .baseAddr => some state.baseAddress
  | .topAddr => some state.topAddress
  | _ => none
termination_by expression => sizeOf expression

/-! ### Word-result constructor equations

The equations below expose the production evaluator's complete wrapped result
for each expression constructor. They are polymorphic in the word carrier and
do not choose a RISC-V target. Equations for `Op`, `Cmp`, `Shift`, and byte
loads deliberately expose the operation fields from `CrepRuntimeState`; they
do not assert that those extra runtime fields equal HOL's word and byte
operations. These remain Flapjack-only projection facts until the source-state
adapter proves that relation. -/

/-- Projection equation for the `Const` case. This is Flapjack-only adapter
infrastructure: it wraps the raw production result as HOL's `word_lab`
constructor, while the full evaluator still uses a target-extended state. -/
theorem evalCrepRuntimeExp_const_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (value : α) :
    (evalCrepRuntimeExp state (.const value)).map PanWordLab.word =
      some (.word value) := by
  simp [evalCrepRuntimeExp]

/-- Projection equation for `Var`. Since `PanWordLab` has exactly the `word`
constructor, projecting and rewrapping the local cell recovers it. This is
Flapjack-only infrastructure, not a claim that its state type is HOL's. -/
theorem evalCrepRuntimeExp_var_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (name : Nat) :
    (evalCrepRuntimeExp state (.var name)).map PanWordLab.word = state.locals name := by
  cases h : state.locals name with
  | none => simp [evalCrepRuntimeExp, h]
  | some cell => cases cell <;> simp [evalCrepRuntimeExp, h, panTheWord]

/-- Projection equation for `LoadGlob`, independent of the target memory
model. This remains Flapjack-only because its state is target-extended. -/
theorem evalCrepRuntimeExp_loadGlob_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (address : BitVec 5) :
    (evalCrepRuntimeExp state (.loadGlob address)).map PanWordLab.word =
      state.globals address := by
  cases h : state.globals address with
  | none => simp [evalCrepRuntimeExp, h]
  | some cell => cases cell <;> simp [evalCrepRuntimeExp, h, panTheWord]

/-- The ordinary `Load` equation uses only the memory function and its domain
predicate. It assumes no byte order or canonical target, but is still an
adapter fact over Flapjack's extended state. -/
theorem evalCrepRuntimeExp_load_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (address : CrepExp α) :
    (evalCrepRuntimeExp state (.load address)).map PanWordLab.word =
      (evalCrepRuntimeExp state address).bind fun value =>
        if state.memaddrs value then some (state.memory value) else none := by
  cases haddr : evalCrepRuntimeExp state address with
  | none => simp [evalCrepRuntimeExp, crepRuntimeLoad, haddr]
  | some value =>
    by_cases hdomain : state.memaddrs value
    · cases hmem : state.memory value with
      | word word => simp [evalCrepRuntimeExp, crepRuntimeLoad, haddr, hdomain, hmem, panTheWord]
    · simp [evalCrepRuntimeExp, crepRuntimeLoad, haddr, hdomain]

/-- Production `LoadByte` projection. The target byte decoder remains visible
in the equation, so this does not claim a HOL `mem_load_byte` correspondence. -/
theorem evalCrepRuntimeExp_loadByte_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (address : CrepExp α) :
    (evalCrepRuntimeExp state (.loadByte address)).map PanWordLab.word =
      (evalCrepRuntimeExp state address).bind fun value =>
        (crepRuntimeLoadByte state value).map PanWordLab.word := by
  simp [evalCrepRuntimeExp, Option.map_bind, Function.comp_def]

/-- Production `Load32` projection. Alignment, byte order, and byte decoding
remain the target model's operations, not HOL premises. -/
theorem evalCrepRuntimeExp_load32_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (address : CrepExp α) :
    (evalCrepRuntimeExp state (.load32 address)).map PanWordLab.word =
      (evalCrepRuntimeExp state address).bind fun value =>
        (crepRuntimeLoad32 state value).map PanWordLab.word := by
  simp [evalCrepRuntimeExp, Option.map_bind, Function.comp_def]

/-- Production list-valued `Op` projection, with the target's word operation
left explicit. This is not a port of HOL `word_op_def` until a target bridge is
proved. -/
theorem evalCrepRuntimeExp_op_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (operator : BinOp)
    (expressions : List (CrepExp α)) :
    (evalCrepRuntimeExp state (.op operator expressions)).map PanWordLab.word =
      (expressions.mapM (evalCrepRuntimeExp state)).bind fun values =>
        (state.memoryModel.wordOp operator values).map PanWordLab.word := by
  simp [evalCrepRuntimeExp, Option.map_bind, Function.comp_def]

/-- Production `Cmp` projection, exposing the target comparison operation. -/
theorem evalCrepRuntimeExp_cmp_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (operator : Cmp)
    (left right : CrepExp α) :
    (evalCrepRuntimeExp state (.cmp operator left right)).map PanWordLab.word = (do
      let leftValue ← evalCrepRuntimeExp state left
      let rightValue ← evalCrepRuntimeExp state right
      pure (.word (state.memoryModel.compare operator leftValue rightValue))) := by
  simp [evalCrepRuntimeExp, Option.map_bind, Function.comp_def]

/-- Production `Shift` projection, exposing the target shift operation. -/
theorem evalCrepRuntimeExp_shift_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (operator : Shift)
    (left right : CrepExp α) :
    (evalCrepRuntimeExp state (.shift operator left right)).map PanWordLab.word = (do
      let leftValue ← evalCrepRuntimeExp state left
      let rightValue ← evalCrepRuntimeExp state right
      (state.memoryModel.shift operator leftValue rightValue).map PanWordLab.word) := by
  simp [evalCrepRuntimeExp, Option.map_bind, Function.comp_def]

/-- The production `CrepOp.mul` equation for every argument-list shape,
expressed with HOL's complete wrapped result type. This is generic in `α` and
uses no target fields, but remains Flapjack-only because the evaluator's state
type is target-extended. -/
theorem evalCrepRuntimeExp_crepOp_mul_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (arguments : List (CrepExp α)) :
    (evalCrepRuntimeExp state (.crepOp .mul arguments)).map PanWordLab.word =
      match arguments with
      | [left, right] => do
          let leftValue ← evalCrepRuntimeExp state left
          let rightValue ← evalCrepRuntimeExp state right
          pure (.word (leftValue * rightValue))
      | _ => none := by
  cases arguments with
  | nil => simp [evalCrepRuntimeExp]
  | cons left rest =>
      cases rest with
      | nil => simp [evalCrepRuntimeExp]
      | cons right rest =>
        cases rest with
        | nil => simp [evalCrepRuntimeExp, crepOpCrep, Option.map_bind, Function.comp_def]
        | cons extra tail => simp [evalCrepRuntimeExp]

/-- Production bridge for `crep_op_def`: the executed `.crepOp .mul` clause is
    `case OPT_MMAP (eval s) args of SOME args' => crep_op op args' | _ => NONE`
    at the only CrepOp constructor `.mul`, i.e. evaluate the two operands and
    apply the tagged `crepOpCrep` directly.
    Malformed arities return `none` on both sides.
    Flapjack-only because the evaluator's state is target-extended. -/
theorem evalCrepRuntimeExp_crepOp_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (operator : CrepOp)
    (arguments : List (CrepExp α)) :
    evalCrepRuntimeExp state (.crepOp operator arguments) =
      (match arguments with
       | [left, right] =>
           (match evalCrepRuntimeExp state left, evalCrepRuntimeExp state right with
            | some leftValue, some rightValue => crepOpCrep operator [leftValue, rightValue]
            | _, _ => none)
       | _ => none) := by
  cases operator
  cases arguments with
  | nil => simp [evalCrepRuntimeExp]
  | cons left rest =>
      cases rest with
      | nil => simp [evalCrepRuntimeExp]
      | cons right rest =>
          cases rest with
          | nil =>
              cases h1 : evalCrepRuntimeExp state left <;>
                cases h2 : evalCrepRuntimeExp state right <;>
                  simp [evalCrepRuntimeExp, crepOpCrep, h1, h2]
          | cons extra tail => simp [evalCrepRuntimeExp]

/-- Projection equation for `BaseAddr`; Flapjack-only because its state is
target-extended. -/
theorem evalCrepRuntimeExp_baseAddr_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) :
    (evalCrepRuntimeExp state .baseAddr).map PanWordLab.word =
      some (.word state.baseAddress) := by
  simp [evalCrepRuntimeExp]

/-- Projection equation for `TopAddr`; Flapjack-only because its state is
target-extended. -/
theorem evalCrepRuntimeExp_topAddr_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) :
    (evalCrepRuntimeExp state .topAddr).map PanWordLab.word =
      some (.word state.topAddress) := by
  simp [evalCrepRuntimeExp]

def crepRuntimeSharedMemExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (operator : CrepMemOp)
    (name : Nat) (address : CrepExp α) : CrepRuntimeStep α σ ε :=
  match evalCrepRuntimeExp state address with
  | some address => crepRuntimeSharedMem handler state operator name address
  | none => (.error, state)

def crepRuntimeExtCallExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : CrepExp α) :
    CrepRuntimeStep α σ ε :=
  match evalCrepRuntimeExp state configuration,
      evalCrepRuntimeExp state configurationLength,
      evalCrepRuntimeExp state array,
      evalCrepRuntimeExp state arrayLength with
  | some configuration, some configurationLength, some array, some arrayLength =>
      crepRuntimeExtCallValues handler state function configuration configurationLength
        array arrayLength
  | _, _, _, _ => (.error, state)

def evalCrepRuntimeExps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : List (CrepExp α) → Option (List α)
  | [] => some []
  | expression :: expressions => do
      let value ← evalCrepRuntimeExp state expression
      let values ← evalCrepRuntimeExps state expressions
      pure (value :: values)
termination_by expressions => sizeOf expressions

/-- HOL-shaped Crep expression evaluator.  HOL's `crepSem$eval` returns a
`word_lab` cell, so this core returns `PanWordLab` results directly instead of
the unwrapped word carrier.  The production unwrapped evaluator
`evalCrepRuntimeExp` has the shape of the `panTheWord` projection of this core;
the formal projection bridge is tracked in bead flapjack-pxn.18.4.3.48.1. -/
def evalCrepRuntimeExpWordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : CrepExp α → Option (PanWordLab α)
  | .const value => some (.word value)
  | .var name => state.locals name
  | .load address => do
      let address ← evalCrepRuntimeExp state address
      (crepRuntimeLoad state address).map PanWordLab.word
  | .load32 address => do
      let address ← evalCrepRuntimeExp state address
      (crepRuntimeLoad32 state address).map PanWordLab.word
  | .loadByte address => do
      let address ← evalCrepRuntimeExp state address
      (crepRuntimeLoadByte state address).map PanWordLab.word
  | .loadGlob address => state.globals address
  | .op operator expressions => do
      let values ← expressions.mapM (evalCrepRuntimeExp state)
      (state.memoryModel.wordOp operator values).map PanWordLab.word
  | .crepOp .mul [left, right] => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (.word (left * right))
  | .cmp operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (.word (state.memoryModel.compare operator left right))
  | .shift operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      (state.memoryModel.shift operator left right).map PanWordLab.word
  | .baseAddr => some (.word state.baseAddress)
  | .topAddr => some (.word state.topAddress)
  | _ => none

/-- List-argument HOL-shaped evaluator: the `word_lab` analogue of
`OPT_MMAP (eval s)` over a list of Crep expressions. -/
def evalCrepRuntimeExpsWordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : List (CrepExp α) → Option (List (PanWordLab α))
  | [] => some []
  | expression :: expressions => do
      let value ← evalCrepRuntimeExpWordLab state expression
      let values ← evalCrepRuntimeExpsWordLab state expressions
      pure (value :: values)
termination_by expressions => sizeOf expressions

/-- Reading the production wrapped cell back through `PanWordLab.word` recovers
it, since `PanWordLab` has the single `word` constructor.  Flapjack-only adapter
infrastructure. -/
theorem optionMapWordPanTheWord (cell : Option (PanWordLab α)) :
    Option.map (fun value => PanWordLab.word (panTheWord value)) cell = cell := by
  cases cell with
  | none => rfl
  | some value => simp [panWordLab_word_panTheWord]

/-- Flapjack-only projection: the production wrapped evaluator's result, read
back through `PanWordLab.word`, is exactly the HOL-shaped `word_lab` core for
every expression constructor.  This is adapter infrastructure, not a HOL port:
the `Op`, `Cmp`, `Shift`, and byte-load cases still delegate to the arbitrary
`CrepRuntimeState` runtime hooks (`memoryModel`) rather than HOL's fixed
`crepSem$eval` word/byte primitives, so no `@[hol]` tag is attached (tracked by
bead flapjack-pxn.18.4.3.48.1). -/
theorem evalCrepRuntimeExp_wordLab_projection
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (expression : CrepExp α) :
    (evalCrepRuntimeExp state expression).map PanWordLab.word =
      evalCrepRuntimeExpWordLab state expression := by
  cases expression <;>
    simp [evalCrepRuntimeExp, evalCrepRuntimeExpWordLab, Function.comp_def,
      Option.map_bind, optionMapWordPanTheWord]
  case crepOp operator args =>
    cases operator
    cases args with
    | nil => simp [evalCrepRuntimeExp]
    | cons left rest =>
        cases rest with
        | nil => simp [evalCrepRuntimeExp]
        | cons right tail =>
            cases tail with
            | nil =>
                simp [evalCrepRuntimeExp, crepOpCrep, Function.comp_def, Option.map_bind]
            | cons extra more =>
                simp [evalCrepRuntimeExp]

theorem optionBindMapListMapWord (values : Option (List α)) (value : α) :
    values.bind (Option.map (List.map PanWordLab.word) ∘ fun rest => some (value :: rest)) =
      (Option.map (List.map PanWordLab.word) values).bind
        (fun rest => some (PanWordLab.word value :: rest)) := by
  cases values <;> simp [Function.comp_def, Option.bind_some]

/-- The production list evaluator read back through `PanWordLab.word` equals the
HOL-shaped list core, for every expression list.  Flapjack-only projection. -/
theorem evalCrepRuntimeExps_wordLab_projection
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (expressions : List (CrepExp α)) :
    (evalCrepRuntimeExps state expressions).map (List.map PanWordLab.word) =
      evalCrepRuntimeExpsWordLab state expressions := by
  induction expressions with
  | nil => simp [evalCrepRuntimeExps, evalCrepRuntimeExpsWordLab]
  | cons expression expressions ih =>
      simp only [evalCrepRuntimeExps, evalCrepRuntimeExpsWordLab]
      have h := evalCrepRuntimeExp_wordLab_projection state expression
      cases hw : evalCrepRuntimeExp state expression with
      | none =>
          have hl : evalCrepRuntimeExpWordLab state expression = none := by
            rw [← h, hw]; rfl
          rw [hl]
          rfl
      | some value =>
          have hl : evalCrepRuntimeExpWordLab state expression = some (PanWordLab.word value) := by
            rw [← h, hw]; rfl
          rw [hl]
          simp [Option.bind_some]
          rw [optionBindMapListMapWord]
          rw [ih]

def restoreCrepRuntimeStep (name : Nat) (oldValue : Option (PanWordLab α)) :
    CrepRuntimeStep α σ ε → CrepRuntimeStep α σ ε
  | (result, state) =>
      (result, { state with locals := resVar state.locals (name, oldValue) })

/-- Pointwise form of the tagged HOL `res_var` update used by the production
    `restoreCrepRuntimeStep`: restoring a variable is an `|+`/`\\` update. -/
@[simp] theorem resVar_locals_apply [BEq α] [LawfulBEq α] (name : Nat)
    (oldValue : Option (PanWordLab α)) (locals : Nat → Option (PanWordLab α)) :
    resVar locals (name, oldValue) =
      fun candidate => if name == candidate then oldValue else locals candidate := by
  cases oldValue with
  | none =>
      funext candidate
      simp only [resVar, FDOMSUB]
  | some v =>
      funext candidate
      simp only [resVar, FUPDATE]

/-- The production Dec restore is the tagged HOL `res_var` update. -/
theorem restoreCrepRuntimeStep_eq_resVar (name : Nat) (oldValue : Option (PanWordLab α))
    (result : CrepRuntimeResult α ε) (state : CrepRuntimeState α σ) :
    restoreCrepRuntimeStep name oldValue (result, state) =
      (result, { state with locals := resVar state.locals (name, oldValue) }) := rfl

def crepRuntimeCallerState (caller callee : CrepRuntimeState α σ) :
    CrepRuntimeState α σ :=
  { caller with
    globals := callee.globals
    code := callee.code
    memory := callee.memory
    memaddrs := callee.memaddrs
    shMemaddrs := callee.shMemaddrs
    clock := callee.clock
    ffiContext := callee.ffiContext
    bigEndian := callee.bigEndian
    ffi := callee.ffi
    baseAddress := callee.baseAddress
    topAddress := callee.topAddress }

/- CakeML's `fix_clock_def` clamps the post-command clock to the smaller of
   the old and new clocks.  Keeping this boundary explicit matters when a
   nested command or FFI handler returns a state with a stale clock. -/
def fixCrepRuntimeClock (oldState : CrepRuntimeState α σ) :
    CrepRuntimeStep α σ ε → CrepRuntimeStep α σ ε
  | (result, newState) =>
      (result, { newState with clock := min oldState.clock newState.clock })

def crepRuntimeCallInfoValid :
    Option (List Nat × Option (α × CrepProg α)) → Bool
  | none => true
  | some (destinations, _) =>
      destinations.eraseDups.length = destinations.length

mutual
  def evalCrepRuntimeCall
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α]
      [ShiftLeft α] [ShiftRight α] [LT α]
      [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (handler : CrepRuntimeFfiHandler α σ ε)
      (primitive : CrepPrimitiveHandler α) :
      Nat → CrepRuntimeState α σ →
        Option (List Nat × Option (α × CrepProg α)) → FunName →
        List (CrepExp α) → Option (CrepRuntimeStep α σ ε)
    | 0, _, _, _, _ => none
    | fuel + 1, caller, info, function, arguments =>
        match evalCrepRuntimeExps caller arguments with
        | none => some (.error, caller)
        | some values =>
            match lookupCrepRuntimeCode function values caller.code with
            | none => some (.error, caller)
            | some (body, calleeLocals) =>
                if !crepRuntimeCallInfoValid info then
                  some (.error, caller)
                else if caller.clock = 0 then
                  some (.timeout, clearCrepRuntimeLocals caller)
                else
                  let callee := decCrepClock
                    { caller with locals := calleeLocals }
                  match evalCrepRuntimeProg handler primitive fuel callee body with
                  | none => none
                  | some (result, callee) =>
                      let (result, callee) := fixCrepRuntimeClock callee (result, callee)
                      let callerState := crepRuntimeCallerState caller callee
                      match result with
                      | .normal => some (.error, callee)
                      | .returned values =>
                          match info with
                          | none =>
                              some (.returned values, clearCrepRuntimeLocals callerState)
                          | some (destinations, _) =>
                              match setCrepRuntimeLocalsExisting
                                  destinations values callerState with
                              | some state' =>
                                  some (.normal, state')
                              | none => some (.error, callee)
                      | .raised exception =>
                          match info with
                          | some (_, some (caught, continuation)) =>
                              if caught == exception then
                                evalCrepRuntimeProg handler primitive fuel
                                  { callerState with locals := caller.locals } continuation
                              else
                                some (.raised exception, clearCrepRuntimeLocals callerState)
                          | _ => some (.raised exception, clearCrepRuntimeLocals callerState)
                      | .broke _label => some (.error, callee)
                      | .continued _label => some (.error, callee)
                      | .error => some (.error, clearCrepRuntimeLocals callerState)
                      | .timeout => some (.timeout, clearCrepRuntimeLocals callerState)
                      | .finalFfi event =>
                          some (.finalFfi event, clearCrepRuntimeLocals callerState)
    termination_by fuel _ _ _ _ => fuel

  def evalCrepRuntimeProg
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α]
      [ShiftLeft α] [ShiftRight α] [LT α]
      [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (handler : CrepRuntimeFfiHandler α σ ε)
      (primitive : CrepPrimitiveHandler α) :
      Nat → CrepRuntimeState α σ → CrepProg α →
        Option (CrepRuntimeStep α σ ε)
    | 0, _, _ => none
    | _fuel + 1, state, .skip => some (.normal, state)
    | fuel + 1, state, .dec name value body =>
        match evalCrepRuntimeExp state value with
        | none => some (.error, state)
        | some value =>
            let nextState := setCrepRuntimeLocal name (.word value) state
            match evalCrepRuntimeProg handler primitive fuel nextState body with
            | none => none
            | some result => some (restoreCrepRuntimeStep name (state.locals name) result)
    | _fuel + 1, state, .assign name value =>
        match evalCrepRuntimeExp state value with
        | none => some (.error, state)
        | some value =>
            match state.locals name with
            | some _ =>
                some (.normal, setCrepRuntimeLocal name (.word value) state)
            | none => some (.error, state)
    | _fuel + 1, state, .primitive names operator arguments =>
        match arguments.mapM (fun name => (state.locals name).map panTheWord) with
        | none => some (.error, state)
        | some arguments =>
            match primitive operator arguments with
            | none => some (.error, state)
            | some values =>
                match setCrepRuntimeLocalsExisting names values state with
                | some state' => some (.normal, state')
                | none => some (.error, state)
    | _fuel + 1, state, .store address value =>
        match evalCrepRuntimeExp state address, evalCrepRuntimeExp state value with
        | some address, some value =>
            match crepRuntimeStore state address value with
            | some state => some (.normal, state)
            | none => some (.error, state)
        | _, _ => some (.error, state)
    | _fuel + 1, state, .store32 address value =>
        match evalCrepRuntimeExp state address, evalCrepRuntimeExp state value with
        | some address, some value =>
            match crepRuntimeStore32 state address value with
            | some state => some (.normal, state)
            | none => some (.error, state)
        | _, _ => some (.error, state)
    | _fuel + 1, state, .storeByte address value =>
        match evalCrepRuntimeExp state address, evalCrepRuntimeExp state value with
        | some address, some value =>
            match crepRuntimeStoreByte state address value with
            | some state => some (.normal, state)
            | none => some (.error, state)
        | _, _ => some (.error, state)
    | _fuel + 1, state, .storeGlob address value =>
        match evalCrepRuntimeExp state value with
        | some value =>
            some (.normal, setCrepRuntimeGlobals address (.word value) state)
        | none => some (.error, state)
    | fuel + 1, state, .seq first second =>
        match evalCrepRuntimeProg handler primitive fuel state first with
        | none => none
        | some result =>
            let (result, state) := fixCrepRuntimeClock state result
            match result with
            | .normal =>
              match evalCrepRuntimeProg handler primitive fuel state second with
              | some result => some result
              | none => none
            | _ => some (result, state)
    | fuel + 1, state, .ite condition thenBranch elseBranch =>
        match evalCrepRuntimeExp state condition with
        | none => some (.error, state)
        | some conditionValue =>
            match evalCrepRuntimeProg handler primitive fuel state
              (if conditionValue != 0 then thenBranch else elseBranch) with
            | some result => some result
            | none => none
    | fuel + 1, state, .while condition body =>
        match evalCrepRuntimeExp state condition with
        | none => some (.error, state)
        | some conditionValue =>
            if conditionValue == 0 then
              some (.normal, state)
            else if state.clock = 0 then
              some (.timeout, clearCrepRuntimeLocals state)
            else
              let decremented := decCrepClock state
              match evalCrepRuntimeProg handler primitive fuel decremented body with
              | none => none
              | some result =>
                  let (result, state) := fixCrepRuntimeClock decremented result
                  match result with
                  | .normal =>
                    match evalCrepRuntimeProg handler primitive fuel state
                    (.while condition body) with
                    | some result => some result
                    | none => none
                  | .continued 0 =>
                    match evalCrepRuntimeProg handler primitive fuel state
                      (.while condition body) with
                    | some result => some result
                    | none => none
                  | .broke 0 => some (.normal, state)
                  | .continued label => some (.continued (label - 1), state)
                  | .broke label => some (.broke (label - 1), state)
                  | result => some (result, state)
    | _fuel + 1, state, .break label => some (.broke label, state)
    | _fuel + 1, state, .continue label => some (.continued label, state)
    | fuel + 1, state, .call info function arguments =>
        evalCrepRuntimeCall handler primitive fuel state info function arguments
    | _fuel + 1, state, .extCall function configuration configurationLength array arrayLength =>
        some (crepRuntimeExtCall handler state function
          configuration configurationLength array arrayLength)
    | _fuel + 1, state, .raise exception =>
        some (.raised exception, clearCrepRuntimeLocals state)
    | _fuel + 1, state, .return values =>
        match evalCrepRuntimeExps state values with
        | some values => some (.returned values, clearCrepRuntimeLocals state)
        | none => some (.error, state)
    | _fuel + 1, state, .shMem operator name address =>
        match operator with
        | .load | .load8 | .load16 | .load32 =>
            match state.locals name with
            | some _ => some (crepRuntimeSharedMemExp handler state operator name address)
            | none => some (.error, state)
        | .store | .store8 | .store16 | .store32 =>
            match state.locals name with
            | some _ => some (crepRuntimeSharedMemExp handler state operator name address)
            | none => some (.error, state)
    | _fuel + 1, state, .tick =>
        if state.clock = 0 then some (.timeout, clearCrepRuntimeLocals state)
        else some (.normal, decCrepClock state)
    termination_by fuel _ _ => fuel
end

/-! General target Call exception-dispatch step.  `hcalleeBody` and
`hhandlerBody` are the recursive-evaluation induction hypotheses for the
callee and compiled handler continuation.  Callee code, argument values,
destinations, exception code, and both programs are arbitrary.  The statement
exposes `crepRuntimeCallerState` and the exact callee clock clamp, and assumes
no execution result for the enclosing Call. -/
theorem evalCrepRuntimeCall_handlesRaisedBody
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (caller : CrepRuntimeState α σ)
    (destinations : List Nat) (caught exception : α)
    (continuation body : CrepProg α) (function : FunName)
    (arguments : List (CrepExp α)) (values : List α)
    (calleeLocals : Nat → Option (PanWordLab α))
    (calleeState : CrepRuntimeState α σ)
    (handlerResult : CrepRuntimeStep α σ ε)
    (harguments : evalCrepRuntimeExps caller arguments = some values)
    (hlookup : lookupCrepRuntimeCode function values caller.code =
      some (body, calleeLocals))
    (hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (caught, continuation))) = true)
    (hclock : caller.clock ≠ 0)
    (hmatch : (caught == exception) = true)
    (hcalleeBody : evalCrepRuntimeProg handler primitive fuel
      (decCrepClock { caller with locals := calleeLocals }) body =
        some (.raised exception, calleeState))
    (hhandlerBody : evalCrepRuntimeProg handler primitive fuel
      { crepRuntimeCallerState caller calleeState with
        locals := caller.locals } continuation = some handlerResult) :
    evalCrepRuntimeCall handler primitive (fuel + 1) caller
      (some (destinations, some (caught, continuation))) function arguments =
        some handlerResult := by
  simp [evalCrepRuntimeCall, harguments, hlookup, hinfoValid, hclock,
    fixCrepRuntimeClock, hmatch, hcalleeBody, hhandlerBody]

/-! `evalCrepRuntimeResult` is fuel bounded: `none` means the supplied target
fuel was exhausted. Semantic `Error` is returned as `some (.error, state)`, so
correctness arguments can choose a sufficient fuel without treating a cutoff
as a program result. -/
def evalCrepRuntimeResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (state : CrepRuntimeState α σ) (program : CrepProg α) :
    Option (CrepRuntimeResult α ε × CrepRuntimeState α σ) :=
  evalCrepRuntimeProg handler primitive fuel state program

theorem crepRuntimeLoad_memaddrs
    (state : CrepRuntimeState α σ) (address : α)
    (haddress : state.memaddrs address = true) :
    crepRuntimeLoad state address = some (panTheWord (state.memory address)) := by
  simp [crepRuntimeLoad, haddress]

theorem crepRuntimeStore_invalid
    [BEq α] (state : CrepRuntimeState α σ) (address value : α)
    (haddress : state.memaddrs address = false) :
    crepRuntimeStore state address value = none := by
  simp [crepRuntimeStore, haddress]

theorem evalCrepRuntimeResult_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ) :
    evalCrepRuntimeResult handler primitive (fuel + 1) state .skip =
      some (.normal, state) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg]


/-- Flapjack-specific analogue of Cake's `flookup_res_var_thm`
(crepPropsScript.sml:257), not an exact HOL port: it is stated with the Boolean
equality that `resVar` is implemented with. -/
theorem FLOOKUP_resVar [BEq α] [LawfulBEq α] (f : FiniteMap α β) (m n : α)
    (v : Option β) :
    FLOOKUP (resVar f (m, v)) n = if n == m then v else FLOOKUP f n := by
  cases v with
  | none =>
    simp only [resVar, FDOMSUB, FLOOKUP]
    by_cases h : n == m
    · have hm : (m == n) = true := by
        rw [beq_iff_eq]
        exact (beq_iff_eq.mp h).symm
      simp only [hm, if_true, h]
    · have hm : (m == n) = false := by
        rw [beq_eq_false_iff_ne]
        intro hc
        exact h (beq_iff_eq.mpr hc.symm)
      simp only [hm, Bool.false_eq_true, if_false, h]
  | some w =>
    simp only [resVar, FUPDATE, FLOOKUP]
    by_cases h : n == m
    · have hm : (m == n) = true := by
        rw [beq_iff_eq]
        exact (beq_iff_eq.mp h).symm
      simp only [hm, if_true, h]
    · have hm : (m == n) = false := by
        rw [beq_eq_false_iff_ne]
        intro hc
        exact h (beq_iff_eq.mpr hc.symm)
      simp only [hm, Bool.false_eq_true, if_false, h]

/-- Flapjack-specific analogue of Cake's `flookup_res_var_diff_eq`
(crepPropsScript.sml:249); not an exact HOL port, since it is stated over the
Boolean-`BEq` `resVar`. -/
theorem FLOOKUP_resVar_diff_eq [BEq α] [LawfulBEq α] (f : FiniteMap α β) (m n : α)
    (v : β) (h : n ≠ m) : FLOOKUP (resVar f (m, some v)) n = FLOOKUP f n := by
  rw [FLOOKUP_resVar]
  have hb : (n == m) = false := by
    rw [beq_eq_false_iff_ne]
    exact h
  simp only [hb, Bool.false_eq_true, if_false]

/-- Flapjack-specific analogue of Cake's `res_var_commutes`
(crepPropsScript.sml:234); not an exact HOL port, since it is stated over the
Boolean-`BEq` `resVar`. -/
theorem resVar_commutes [BEq α] [LawfulBEq α] (lc lc' : FiniteMap α β) (n h : α)
    (hne : n ≠ h) :
    resVar (resVar lc (h, FLOOKUP lc' h)) (n, FLOOKUP lc' n) =
    resVar (resVar lc (n, FLOOKUP lc' n)) (h, FLOOKUP lc' h) := by
  cases hh : FLOOKUP lc' h with
  | none =>
    cases hn : FLOOKUP lc' n with
    | none =>
      simp only [resVar]
      rw [FDOMSUB_commutes lc n h hne]
    | some vn =>
      simp only [resVar]
      rw [FDOMSUB_FUPDATE_neq lc h n vn hne.symm]
  | some vh =>
    cases hn : FLOOKUP lc' n with
    | none =>
      simp only [resVar]
      rw [FDOMSUB_FUPDATE_neq lc n h vh hne]
    | some vn =>
      simp only [resVar]
      rw [FUPDATE_comm lc h vh n vn hne.symm]

/-- Flapjack-specific analogue of Cake's `flookup_res_var_distinct_eq`
(crepPropsScript.sml:763); not an exact HOL port, since it is stated over this
file's `resVar`: folding `res_var` over a list whose keys do not contain `x`
leaves `x` untouched. -/
theorem FLOOKUP_foldl_resVar_not_mem [BEq α] [LawfulBEq α]
    (xs : List (α × Option β)) (f : FiniteMap α β) (x : α)
    (h : x ∉ xs.map Prod.fst) :
    FLOOKUP (xs.foldl resVar f) x = FLOOKUP f x := by
  induction xs generalizing f with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, hrest⟩ := h
    rw [List.foldl_cons, ih (resVar f entry) hrest, FLOOKUP_resVar]
    have hfalse : (x == entry.1) = false := beq_eq_false_iff_ne.mpr hne
    simp [hfalse]

/-- Flapjack-specific analogue of Cake's `flookup_res_var_distinct_zip_eq`
(crepPropsScript.sml:777); not an exact HOL port: the zipped form of
`FLOOKUP_foldl_resVar_not_mem`. -/
theorem FLOOKUP_foldl_resVar_zip_not_mem [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List (Option β)) (f : FiniteMap α β) (x : α)
    (hlen : xs.length = ys.length) (h : x ∉ xs) :
    FLOOKUP ((xs.zip ys).foldl resVar f) x = FLOOKUP f x := by
  apply FLOOKUP_foldl_resVar_not_mem
  rw [List.map_fst_zip (by omega)]
  exact h

/-- Flapjack-specific analogue of Cake's `flookup_res_var_distinct`
(crepPropsScript.sml:796); not an exact HOL port: looking up a key list disjoint
from the updated key list is unaffected by the fold. -/
theorem map_FLOOKUP_foldl_resVar_zip [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List α) (zs : List (Option β)) (f : FiniteMap α β)
    (hdisj : ListDisjoint xs ys) (hlen : xs.length = zs.length) :
    ys.map (fun y => FLOOKUP ((xs.zip zs).foldl resVar f) y) =
      ys.map (fun y => FLOOKUP f y) := by
  revert hdisj
  induction ys with
  | nil => intro _; rfl
  | cons y rest ih =>
    intro hdisj
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · exact FLOOKUP_foldl_resVar_zip_not_mem xs zs f y hlen
        (fun hy => hdisj y hy (by simp))
    · exact ih (fun v hv hmem => hdisj v hv (by simp [hmem]))

theorem map_FLOOKUP_foldl_resVar_zip_fupdate [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List α) (as : List β) (cs : List (Option β))
    (fm : FiniteMap α β) (hdisj : ListDisjoint xs ys)
    (hlenAs : xs.length = as.length) (hlenCs : xs.length = cs.length) :
    ys.map (fun y => FLOOKUP ((xs.zip cs).foldl resVar (FUPDATE_LIST fm (xs.zip as))) y) =
      ys.map (fun y => FLOOKUP fm y) := by
  rw [map_FLOOKUP_foldl_resVar_zip xs ys cs (FUPDATE_LIST fm (xs.zip as)) hdisj hlenCs]
  exact map_FLOOKUP_FUPDATE_LIST_zip_not_mem xs ys as fm hdisj hlenAs

/-- Flapjack-specific analogue of Cake `res_var_lookup_original_eq`
(crepPropsScript.sml:612); not an exact HOL port, since it is stated over this
file's `resVar`: folding `res_var` over the `ZIP` of a distinct key list with its
values, restoring each key's original binding, reproduces the original map. -/
theorem foldl_resVar_zip_lookup_original [BEq α] [LawfulBEq α]
    (xs : List α) (ys : List β) (lc : FiniteMap α β)
    (hdistinct : xs.Nodup) (hlen : xs.length = ys.length) :
    ((xs.zip (xs.map (FLOOKUP lc))).foldl resVar
        (FUPDATE_LIST lc (xs.zip ys))) = lc := by
  induction xs generalizing ys lc with
  | nil =>
    cases ys with
    | nil => simp [FUPDATE_LIST_nil]
    | cons y ys => simp at hlen
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [List.nodup_cons] at hdistinct
      obtain ⟨ha, hdistinctTail⟩ := hdistinct
      have hlenTail : xs.length = ys.length := by simpa using hlen
      have hnotmem : a ∉ (xs.zip ys).map Prod.fst := by
        rw [List.map_fst_zip (by omega)]
        exact ha
      simp only [List.map_cons, List.zip_cons_cons, FUPDATE_LIST_cons, List.foldl_cons]
      rw [← FUPDATE_FUPDATE_LIST_commutes lc a y (xs.zip ys) hnotmem]
      cases hlookup : FLOOKUP lc a with
      | none =>
        simp only [resVar, FDOMSUB_FUPDATE_same]
        rw [FDOMSUB_FUPDATE_LIST_commutes xs ys lc a ha hlenTail,
            FDOMSUB_eq_self_of_lookup_none lc a hlookup]
        exact ih ys lc hdistinctTail hlenTail
      | some v =>
        simp only [resVar]
        rw [FUPDATE_FUPDATE_same]
        rw [FUPDATE_eq_self_of_lookup_some (FUPDATE_LIST lc (xs.zip ys)) a v
          (by rw [FLOOKUP_FUPDATE_LIST_zip_not_mem xs ys lc a hlenTail ha]; exact hlookup)]
        exact ih ys lc hdistinctTail hlenTail

end Flapjack
