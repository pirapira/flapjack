import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.Pancake.Semantics.CrepSem.LookupCode
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.CrepArith
import Flapjack.FfiHOL

/-!
Expression-observation projection from the repository's existing named Crep
field carriers to the evaluator's `CrepHolState`. This is Flapjack-only
support, not a second Crep state datatype or a port of `crepSem$state`: code
and FFI fields are accepted as arguments but omitted because expression
evaluation does not inspect them.

The projection reuses `CrepLocalsExact`, `CrepCodeMapExact`, `HolWordLab`,
`MlString`, and `HolFfiState`. The map aliases still encode lookup as a plain
function and carry no finite-support witness; therefore this is not a faithful
whole-state representation. Memory remains total and the word domain is the
canonical `Fin width` representation. The evaluator correspondence and exact
HOL state-record relation remain open; this module carries no `@[hol]` tag.
-/

namespace Flapjack

/-- Project the sole constructor of exact HOL `word_lab` to the evaluator's
    `PanWordLab` over canonical finite Boolean words. -/
def holWordLabToCrepSourceWordLab {width : Nat}
    (value : HolWordLab width) : PanWordLab (Fin width → Bool) :=
  match value with
  | .word bits => .word (bitVecToHolWordBits bits)

@[simp] theorem panWordLabWord_panTheWord_holWordLabToCrepSourceWordLab
    {width : Nat} (value : HolWordLab width) :
    PanWordLab.word (panTheWord (holWordLabToCrepSourceWordLab value)) =
      holWordLabToCrepSourceWordLab value := by
  cases value
  rfl

/-- Project the exact expression-observable fields of a Crep state into the
    existing source evaluator state. The exact `code` and `ffi` fields are
    accepted to keep this projection tied to the complete HOL field telescope;
    they are not converted because expression evaluation is independent of
    both. `_runtimeFfi` is a compatibility argument and is discarded too; the
    projected evaluator uses an inert `Unit` FFI state. -/
def crepSourceEvalStateOfHOLFields {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (_code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool)
    (_ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width)
    (_runtimeFfi : FfiState Unit) :
    CrepHolState (Fin width → Bool) Unit :=
  { locals := fun name => (FLOOKUP locals name).map holWordLabToCrepSourceWordLab
    globals := fun name => (FLOOKUP globals name).map holWordLabToCrepSourceWordLab
    code := fun _ => none
    memory := fun address =>
      holWordLabToCrepSourceWordLab (memory (holWordBitsToBitVec address))
    memaddrs := fun address => decide (memaddrs (holWordBitsToBitVec address))
    shMemaddrs := fun address => decide (shMemaddrs (holWordBitsToBitVec address))
    clock := clock
    bigEndian := bigEndian
    ffi := natCrepRuntimeFfiState
    baseAddress := bitVecToHolWordBits baseAddress
    topAddress := bitVecToHolWordBits topAddress }

/-- Translate exact HOL expression syntax into the source evaluator's
    canonical `Fin width → Bool` carrier. -/
def crepExpHOLToSourceBits {width : Nat} [NeZero width] :
    CrepExpHOL width → CrepExp (Fin width → Bool) :=
  fun expression =>
    mapCrepExpWord bitVecToHolWordBits (crepExpOfHOL expression)

/-- Interpret `simp_exp` over the exact width-indexed syntax and transport its
    result to the canonical finite-Boolean source word carrier. -/
def crepSimpExpHOLToSourceBits {width : Nat} [NeZero width]
    (expression : CrepExpHOL width) : CrepExp (Fin width → Bool) :=
  mapCrepExpWord bitVecToHolWordBits
    (crepSimpExp (BitVec.ofNat width) (crepExpOfHOL expression))

/-- HOL `FMAP_MAP2` code update on the exact Crep code-map carrier. The
    expression evaluator projection erases this field, as the HOL `eval_def`
    clauses do not inspect code. -/
def crepCodeMapMap2Exact {width : Nat} [NeZero width]
    (f : Flapjack.Basis.Pure.MlString.MlString ×
      (List Nat × CrepProgHOL width) → List Nat × CrepProgHOL width)
    (code : CrepCodeMapExact width) : CrepCodeMapExact width :=
  fun name => (code name).map (fun entry => f (name, entry))

/-- The field projection discards only code and FFI, so HOL's arbitrary
    `mapc f` code update and any exact FFI replacement leave its expression
    observation unchanged. -/
theorem crepSourceEvalStateOfHOLFields_codeFfiIrrel
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (f : Flapjack.Basis.Pure.MlString.MlString ×
      (List Nat × CrepProgHOL width) → List Nat × CrepProgHOL width)
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool)
    (ffi ffi' : HolFfiState σ)
    (baseAddress topAddress : BitVec width)
    (_runtimeFfi runtimeFfi' : FfiState Unit) :
    crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress _runtimeFfi =
      crepSourceEvalStateOfHOLFields locals globals
        (crepCodeMapMap2Exact f code) memory memaddrs shMemaddrs
        clock bigEndian ffi' baseAddress topAddress runtimeFfi' := rfl

/-- Flapjack projection equation for exact-source local lookup. There is no
    standalone HOL theorem for this projection helper. -/
@[simp] theorem crepSourceEvalStateOfHOLFields_locals
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width) (runtimeFfi : FfiState Unit)
    (name : Nat) :
    (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
      clock bigEndian ffi baseAddress topAddress runtimeFfi).locals name =
        (FLOOKUP locals name).map holWordLabToCrepSourceWordLab := rfl

/-- Flapjack projection equation for exact-source global lookup. There is no
    standalone HOL theorem for this projection helper. -/
@[simp] theorem crepSourceEvalStateOfHOLFields_globals
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width) (runtimeFfi : FfiState Unit)
    (name : BitVec 5) :
    (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
      clock bigEndian ffi baseAddress topAddress runtimeFfi).globals name =
        (FLOOKUP globals name).map holWordLabToCrepSourceWordLab := rfl

/-- Flapjack projection equation for exact-source memory-domain membership.
    It is representation support, not a standalone HOL theorem. -/
@[simp] theorem crepSourceEvalStateOfHOLFields_memaddrs
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemAddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemAddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width) (runtimeFfi : FfiState Unit)
    (address : Fin width → Bool) :
    (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemAddrs
      clock bigEndian ffi baseAddress topAddress runtimeFfi).memaddrs address =
        decide (memaddrs (holWordBitsToBitVec address)) := rfl

/-- Flapjack projection equation for the total memory field. It is
    representation support, not a standalone HOL theorem. -/
@[simp] theorem crepSourceEvalStateOfHOLFields_memory
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width) (runtimeFfi : FfiState Unit)
    (address : Fin width → Bool) :
    (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
      clock bigEndian ffi baseAddress topAddress runtimeFfi).memory address =
        holWordLabToCrepSourceWordLab (memory (holWordBitsToBitVec address)) := rfl

/-! These five untagged equations match the corresponding leaf clauses in
    HOL `crepSem$eval_def`. They are stated over the existing exact field
    carriers but evaluate through the explicit observation projection. The
    enclosing arbitrary-state evaluator identity is still unproved. -/

/-- Const clause equation for the projected source evaluator. It follows the
    `eval_def` Const clause, but is not a standalone HOL theorem because it is
    stated through the Flapjack projection. -/
theorem evalCrepSourceProjection_const
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width) (runtimeFfi : FfiState Unit)
    (value : BitVec width) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress runtimeFfi)
      (crepExpHOLToSourceBits (.const value)) =
        some (.word (bitVecToHolWordBits value)) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
    crepExpOfHOL, mapCrepExpWord]

/-- Var clause equation for the projected source evaluator. It follows the
    `eval_def` Var clause, but is not a standalone HOL theorem because it is
    stated through the Flapjack projection. -/
theorem evalCrepSourceProjection_var
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width) (runtimeFfi : FfiState Unit)
    (name : Nat) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress runtimeFfi)
      (crepExpHOLToSourceBits (.var name)) =
        (FLOOKUP locals name).map holWordLabToCrepSourceWordLab := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
    crepExpOfHOL, mapCrepExpWord, crepSourceEvalStateOfHOLFields,
    holWordLabToCrepSourceWordLab, Function.comp_def]
  apply congrArg (fun convert => Option.map convert (FLOOKUP locals name))
  funext value
  cases value
  rfl

/-- Load clause equation for the projected source evaluator. It follows the
    `eval_def`/`mem_load_def` clauses, but is not a standalone HOL theorem
    because it is stated through the Flapjack projection. -/
theorem evalCrepSourceProjection_load
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress address : BitVec width)
    (runtimeFfi : FfiState Unit)
    (addressExpression : CrepExpHOL width)
    (hAddress : evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress runtimeFfi)
      (crepExpHOLToSourceBits addressExpression) =
        some (bitVecToHolWordBits address)) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress runtimeFfi)
      (crepExpHOLToSourceBits (.load addressExpression)) =
        if memaddrs address then
          some (holWordLabToCrepSourceWordLab (memory address)) else none := by
  have hLoad : crepExpHOLToSourceBits (.load addressExpression) =
      .load (crepExpHOLToSourceBits addressExpression) := by
    simp [crepExpHOLToSourceBits, crepExpOfHOL, mapCrepExpWord]
  rw [hLoad]
  change (evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress runtimeFfi)
      (.load (crepExpHOLToSourceBits addressExpression))).map PanWordLab.word = _
  simp only [evalCrepHolFiniteWordSourceExp]
  rw [hAddress]
  simp [crepSourceEvalStateOfHOLFields, holWordLabToCrepSourceWordLab,
    panTheWord]
  rw [holWordBitsToBitVec_bitVecToHolWordBits]

/-- LoadGlob clause equation for the projected source evaluator. It follows
    `eval_def`, but is not a standalone HOL theorem because it is stated through
    the Flapjack projection. -/
theorem evalCrepSourceProjection_loadGlob
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width) (runtimeFfi : FfiState Unit)
    (name : BitVec 5) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress runtimeFfi)
      (crepExpHOLToSourceBits (.loadGlob name)) =
        (FLOOKUP globals name).map holWordLabToCrepSourceWordLab := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
    crepExpOfHOL, mapCrepExpWord, crepSourceEvalStateOfHOLFields,
    holWordLabToCrepSourceWordLab, Function.comp_def]
  apply congrArg (fun convert => Option.map convert (FLOOKUP globals name))
  funext value
  cases value
  rfl

/-- BaseAddr clause equation for the projected source evaluator. It follows
    `eval_def`, but is not a standalone HOL theorem because it is stated through
    the Flapjack projection. -/
theorem evalCrepSourceProjection_baseAddr
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width) (runtimeFfi : FfiState Unit) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress runtimeFfi)
      (crepExpHOLToSourceBits .baseAddr) =
        some (.word (bitVecToHolWordBits baseAddress)) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
    crepExpOfHOL, mapCrepExpWord, crepSourceEvalStateOfHOLFields]

/-- TopAddr clause equation for the projected source evaluator. It follows
    `eval_def`, but is not a standalone HOL theorem because it is stated through
    the Flapjack projection. -/
theorem evalCrepSourceProjection_topAddr
    {width : Nat} [NeZero width] {σ : Type}
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width) (runtimeFfi : FfiState Unit) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress runtimeFfi)
      (crepExpHOLToSourceBits .topAddr) =
        some (.word (bitVecToHolWordBits topAddress)) := by
  simp [evalCrepHolFiniteWordSourceExpWordLab,
    evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
    crepExpOfHOL, mapCrepExpWord, crepSourceEvalStateOfHOLFields]

/-- All-width `simp_exp_correct1` Var case over the existing named Crep field
    carriers and the expression-observation projection. The unused HOL result
    binder, successful-evaluation premise, exact `FMAP_MAP2` code update, and
    complete optional `word_lab` result are retained. This remains untagged:
    the lookup aliases lack finite-support witnesses, and the source evaluator
    is not yet identified with native `crepSem$eval` on one exact state type. -/
theorem crepSimpExpCorrect1SourceProjection_var
    {width : Nat} [NeZero width] {σ : Type}
    (f : Flapjack.Basis.Pure.MlString.MlString ×
      (List Nat × CrepProgHOL width) → List Nat × CrepProgHOL width)
    (locals : CrepLocalsExact width)
    (globals : FiniteMap (BitVec 5) (HolWordLab width))
    (code : CrepCodeMapExact width)
    (memory : BitVec width → HolWordLab width)
    (memaddrs shMemaddrs : BitVec width → Prop)
    [DecidablePred memaddrs] [DecidablePred shMemaddrs]
    (clock : Nat) (bigEndian : Bool) (ffi : HolFfiState σ)
    (baseAddress topAddress : BitVec width)
    (_result : HolWordLab width) (name : Nat)
    (_h : evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress natCrepRuntimeFfiState)
      (crepExpHOLToSourceBits (.var name)) ≠ none) :
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals
        (crepCodeMapMap2Exact f code) memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress natCrepRuntimeFfiState)
      (crepSimpExpHOLToSourceBits (.var name)) =
    evalCrepHolFiniteWordSourceExpWordLab
      (instFinHolFiniteDimension (width := width))
      (crepSourceEvalStateOfHOLFields locals globals code memory memaddrs shMemaddrs
        clock bigEndian ffi baseAddress topAddress natCrepRuntimeFfiState)
      (crepExpHOLToSourceBits (.var name)) := by
  have hState := crepSourceEvalStateOfHOLFields_codeFfiIrrel
    locals globals f code memory memaddrs shMemaddrs clock bigEndian ffi ffi
    baseAddress topAddress natCrepRuntimeFfiState natCrepRuntimeFfiState
  rw [hState]
  simp [crepSimpExpHOLToSourceBits, crepExpHOLToSourceBits,
    crepExpOfHOL, mapCrepExpWord, crepSimpExp]

end Flapjack
