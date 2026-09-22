import Flapjack.CrepeProgramInduction
import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramGenericStoreStateCorrectness
import Flapjack.CrepeProgramIteCorrectness
import Flapjack.CrepeProgramRaiseCorrectness
import Flapjack.CrepeProgramStoreCorrectness
import Flapjack.CrepeProgramStoreByteCorrectness
import Flapjack.CrepeProgramWhileCorrectness
import Flapjack.CrepeProgramSourceWordReturnCorrectness
import Flapjack.CompileCalleeParameterFreshness
import Flapjack.PanToCrepMaxList

/-!
The checked Lean boundary corresponding to CakeML's
`pan_to_crepProofScript.sml` theorem `pc_compile_correct` (line 442).

The compact `PanValueControlResult` evaluator predates the clocked/FFI
boundary and therefore cannot express `TimeOut` or `FinalFFI`.  This module
keeps the existing source-to-Crep state, global, memory, exception, and
flattened-value relations, while adding those two result cases explicitly.
The evaluator obligations are parameters: the theorem below is the
kernel-checked assembly boundary to be discharged by the source and Crep
semantic proofs for each supported compiler subset.  The current
`panValueCrepStateRel` is deliberately a supported-empty-global relation
(`sourceGlobals = fun _ => none`); the code and exception-shape relations,
`globalsLookup`, and the localised-program premise remain explicit parameters
until global lowering is completed.
-/

namespace Flapjack

/-! Source-side result cases from HOL `pc_compile_correct`, including the
`Error` case excluded by that theorem's premise. -/
inductive PanValuePcResult (α : Type u) where
  | error
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (values : List (PanValue α))
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (exception : ExceptionId)
      (value : PanValue α)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | timeout (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | finalFfi (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (event : FfiFinalEvent)

/-! Crep-side result cases are the corresponding target observations.  The
target `error` constructor is retained so the boundary can state the HOL
non-error premise symmetrically, even though the current full Crep evaluator
reports failures through `none`. -/
inductive CrepPcResult (α : Type u) where
  | error
  | normal (state : CrepState α)
  | returned (state : CrepState α) (values : List α)
  | raised (state : CrepState α) (exception : α)
  | broke (state : CrepState α) (label : Nat)
  | continued (state : CrepState α) (label : Nat)
  | timeout (state : CrepState α)
  | finalFfi (state : CrepState α) (event : FfiFinalEvent)

abbrev PanValuePcSourceCode α :=
  List (FunName × List VarName × Prog α)

abbrev PanValuePcTargetCode α :=
  List (CompiledFunction α)

abbrev PanValuePcCodeRel α :=
  CompileContext α → PanValuePcSourceCode α → PanValuePcTargetCode α → Prop

/-- Concrete Cake `code_rel` analogue (`pan_to_crepProofScript.sml:32`).

Every source function's compiled target image is present with the parameter
slots and body produced by the function-local compile context, and the source
body is localised.  This is the missing glue between the abstract
`PanValuePcCodeRel` parameter of `pc_compile_correct` and the concrete compiler
table: it has exactly the type of `PanValuePcCodeRel α`, so it can be passed
directly as the `codeRel` argument. -/
def panValuePcCodeRelConcrete [BEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α)
    (source : PanValuePcSourceCode α) (target : PanValuePcTargetCode α) : Prop :=
  ∀ name parameters body,
    lookupPanFunction name source = some (parameters, body) →
    localisedProg body ∧
      ∃ vshs returnShape,
      lookupInfo name context.functions = some (vshs, returnShape) ∧
      vshs.map Prod.fst = parameters ∧
      lookupCompiledFunction name target =
        some (panToCrepVars vshs,
          panToCrepCompFunc context vshs body)

/-- The empty source code satisfies the concrete code relation for any target. -/
theorem panValuePcCodeRelConcrete_nil [BEq String] [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (target : PanValuePcTargetCode α) :
    panValuePcCodeRelConcrete context [] target := by
  intro name parameters body hlookup
  simp [lookupPanFunction] at hlookup

/-- A concrete code relation exposes localisation of every looked-up source
body, which is the localisation obligation of Cake `mk_ctxt_code_imp_code_rel`. -/
theorem panValuePcCodeRelConcrete_localised [BEq String] [BEq α] [OfNat α 0]
    [Add α] {context : CompileContext α} {source : PanValuePcSourceCode α}
    {target : PanValuePcTargetCode α}
    (h : panValuePcCodeRelConcrete context source target) :
    ∀ name parameters body,
      lookupPanFunction name source = some (parameters, body) →
      localisedProg body :=
  fun name parameters body hlookup => (h name parameters body hlookup).1

abbrev PanValuePcExceptionShapeRel α :=
  CompileContext α → InfoMap Shape → InfoMap Shape → Prop

/-- Concrete Cake `excp_rel` analogue (`pan_to_crepProofScript.sml:16`),
adapted to the shape-valued exception table of this boundary: the source and
target exception shape maps agree on every lookup, i.e. they have the same
finite domain and the same payload shapes.  This has exactly the type of
`PanValuePcExceptionShapeRel α`, so it can be passed directly as the `excpRel`
argument of `pc_compile_correct`. -/
def panValuePcExceptionShapeRelConcrete (_context : CompileContext α)
    (sourceEshapes targetEshapes : InfoMap Shape) : Prop :=
  ∀ exception shape,
    lookupInfo exception sourceEshapes = some shape ↔
      lookupInfo exception targetEshapes = some shape

/-- The concrete exception-shape relation is reflexive. -/
theorem panValuePcExceptionShapeRelConcrete_refl (context : CompileContext α)
    (eshapes : InfoMap Shape) :
    panValuePcExceptionShapeRelConcrete context eshapes eshapes := by
  unfold panValuePcExceptionShapeRelConcrete
  intro exception shape
  rfl

/-- Cake `ctxt_max_def` (`pan_commonPropsScript.sml:11`) port: the slot bound
recorded by `mk_ctxt`/`ctxt_fc` holds for every variable slot. -/
def panValueCtxtMax [BEq String] (bound : Nat)
    (vars : InfoMap (Shape × List Nat)) : Prop :=
  0 ≤ bound ∧
    ∀ name shape slots, lookupInfo name vars = some (shape, slots) →
      ∀ slot ∈ slots, slot ≤ bound

/-- Cake `no_overlap_def` (`pan_commonPropsScript.sml:18`) port: within each
variable the slots are duplicate-free, and slots of two distinct variables
cannot share a slot number. -/
def panValueNoOverlap [BEq String] (vars : InfoMap (Shape × List Nat)) : Prop :=
  (∀ name shape slots, lookupInfo name vars = some (shape, slots) → slots.Nodup) ∧
    ∀ name name' shape shape' slots slots',
      lookupInfo name vars = some (shape, slots) →
      lookupInfo name' vars = some (shape', slots') →
      (∃ slot, slot ∈ slots ∧ slot ∈ slots') → name = name'

/-- The empty variable map satisfies Cake's `ctxt_max`. -/
theorem panValueCtxtMax_empty [BEq String] (bound : Nat) (hbound : 0 ≤ bound) :
    panValueCtxtMax bound ([] : InfoMap (Shape × List Nat)) := by
  refine ⟨hbound, ?_⟩
  intro name shape slots hlookup
  simp [lookupInfo] at hlookup

/-- The empty variable map satisfies Cake's `no_overlap`. -/
theorem panValueNoOverlap_empty [BEq String] :
    panValueNoOverlap ([] : InfoMap (Shape × List Nat)) := by
  refine ⟨?_, ?_⟩
  · intro name shape slots hlookup
    simp [lookupInfo] at hlookup
  · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
    simp [lookupInfo] at hlookup

/-- Counterpart of Cake `no_overlap_flookup_distinct`
    (`cakeml/pancake/semantics/pan_commonPropsScript.sml`): two distinct
    variables of a `no_overlap` context have disjoint slot lists. -/
theorem panValueNoOverlap_lookup_disjoint [BEq String] [LawfulBEq String]
    (vars : InfoMap (Shape × List Nat)) (name name' : String)
    (shape shape' : Shape) (slots slots' : List Nat)
    (hoverlap : panValueNoOverlap vars) (hne : name ≠ name')
    (hlookup : lookupInfo name vars = some (shape, slots))
    (hlookup' : lookupInfo name' vars = some (shape', slots')) :
    ListDisjoint slots slots' := by
  intro value hin hin'
  exact hne (hoverlap.2 name name' shape shape' slots slots'
    hlookup hlookup' ⟨value, hin, hin'⟩)

/-- Counterpart of Cake `all_distinct_alist_no_overlap`
    (`cakeml/pancake/semantics/panPropsScript.sml`): the `(variable, shape,
    slot-list)` alist built by splitting a nodup flat slot list with
    `withShape` satisfies `panValueNoOverlap`. -/
theorem panValueNoOverlap_zip_withShape [LawfulBEq String]
    (ns : List Nat) (vs : List VarName) (sh : List Shape)
    (hns : ns.Nodup)
    (hlen : ns.length = Shape.shapeSize (.comb sh))
    (hlenv : vs.length = sh.length) :
    panValueNoOverlap (vs.zip (sh.zip (withShape sh ns))) := by
  constructor
  · intro name shape slots hlookup
    have hmem := lookupInfo_some_mem name
      (vs.zip (sh.zip (withShape sh ns))) (shape, slots) hlookup
    obtain ⟨i, hi, _hj, _hfirst, hsecond⟩ :=
      mem_zip_getElem vs (sh.zip (withShape sh ns)) (name, (shape, slots)) hmem
    rw [List.getElem_zip] at hsecond
    have hiShapes : i < sh.length := by rw [hlenv] at hi; exact hi
    have hiValues : i < (withShape sh ns).length := by
      rw [withShape_length]; exact hiShapes
    have hcomponent : slots = (withShape sh ns)[i]'hiValues := by
      simpa using (congrArg Prod.snd hsecond).symm
    rw [hcomponent]
    exact all_distinct_withShape sh ns i hns hiShapes hlen
  · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
    by_cases hneName : name = name'
    · exact hneName
    · exfalso
      obtain ⟨slot, hslot, hslot'⟩ := hcommon
      have hmem := lookupInfo_some_mem name
        (vs.zip (sh.zip (withShape sh ns))) (shape, slots) hlookup
      have hmem' := lookupInfo_some_mem name'
        (vs.zip (sh.zip (withShape sh ns))) (shape', slots') hlookup'
      have hdisj := listDisjoint_of_mem_zip_withShape vs sh ns
        (name, (shape, slots)) (name', (shape', slots'))
        hlenv (by rw [withShape_length]) hns hlen hmem hmem' hneName
      exact hdisj slot hslot hslot'

/-! Counterpart of Cake's `all_distinct_alist_ctxt_max`
    (`cakeml/pancake/semantics/panPropsScript.sml`): the `(variable, shape,
    slot-list)` alist built by splitting a flat slot list with `withShape`
    satisfies `panValueCtxtMax` at `maxList ns`. -/
theorem panValueCtxtMax_zip_withShape [LawfulBEq String]
    (ns : List Nat) (vs : List VarName) (sh : List Shape)
    (_hns : ns.Nodup)
    (hlen : ns.length = Shape.shapeSize (.comb sh))
    (hlenv : vs.length = sh.length) :
    panValueCtxtMax (maxList ns) (vs.zip (sh.zip (withShape sh ns))) := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro name shape slots hlookup slot hslot
  have hmem := lookupInfo_some_mem name
    (vs.zip (sh.zip (withShape sh ns))) (shape, slots) hlookup
  obtain ⟨i, hi, _hj, _hfirst, hsecond⟩ :=
    mem_zip_getElem vs (sh.zip (withShape sh ns)) (name, (shape, slots)) hmem
  rw [List.getElem_zip] at hsecond
  have hiShapes : i < sh.length := by rw [hlenv] at hi; exact hi
  have hiValues : i < (withShape sh ns).length := by
    rw [withShape_length]; exact hiShapes
  have hcomponent : slots = (withShape sh ns)[i]'hiValues := by
    simpa using (congrArg Prod.snd hsecond).symm
  rw [hcomponent] at hslot
  exact maxList_ge_of_mem ns slot
    (mem_of_withShape_mem sh ns i slot hiValues hlen hslot)

/-! The compiler-generated formal-parameter map satisfies the Cake `no_overlap`
    invariant.  The proof reuses the source-shaped parameter-list allocation
    theorem, then transports it through the metadata equation and the
    list-backed finite-map lookup. -/
theorem panValueNoOverlap_compileParamVars
    [LawfulBEq String]
    (params : List (VarName × Shape)) (offset : Nat) :
    panValueNoOverlap ((compileParamVars params offset).1.reverse) := by
  let values : List (PanValue Unit) := params.map (fun _ => PanValue.word ())
  have hlength : params.length = values.length := by
    simp [values]
  have hpair := compileCalleeParameterList_slots_pairwise_disjoint
    params values offset hlength
  have hrel := pairwise_symmetric_relation_of_mem
    (fun left right : CalleeParameter Unit =>
      ∀ slot ∈ left.slots, slot ∉ right.slots)
    (compileCalleeParameterList params values offset) hpair
  have hmetadata := compileCalleeParameterList_metadata params values offset hlength
  have hdistinct : ∀ names : List Nat, CrepDistinctNames names → names.Nodup := by
    intro names
    induction names with
    | nil => simp
    | cons name names ih =>
        intro h
        rcases h with ⟨hnot, htail⟩
        exact List.pairwise_cons.mpr ⟨
          (fun other hmem heq => hnot (heq ▸ hmem)),
          ih htail⟩
  have rawMem : ∀ name shape slots,
      lookupInfo name (compileParamVars params offset).1.reverse =
        some (shape, slots) →
      (name, (shape, slots)) ∈ (compileParamVars params offset).1 := by
    intro name shape slots hlookup
    have hmem := lookupInfo_some_mem name
      (compileParamVars params offset).1.reverse (shape, slots) hlookup
    exact List.mem_reverse.mp hmem
  constructor
  · intro name shape slots hlookup
    have hmemRaw := rawMem name shape slots hlookup
    rw [← hmetadata] at hmemRaw
    obtain ⟨parameter, hparameter, hentry⟩ := List.mem_map.mp hmemRaw
    have hslots := compileCalleeParameterList_distinct_slots
      params values offset hlength parameter hparameter
    have hslots' : slots = parameter.slots :=
      congrArg Prod.snd (congrArg Prod.snd hentry).symm
    rw [hslots']
    exact hdistinct parameter.slots hslots
  · intro name name' shape shape' slots slots' hlookup hlookup' hcommon
    have hmemRaw := rawMem name shape slots hlookup
    have hmemRaw' := rawMem name' shape' slots' hlookup'
    rw [← hmetadata] at hmemRaw hmemRaw'
    obtain ⟨left, hleft, hleftEq⟩ := List.mem_map.mp hmemRaw
    obtain ⟨right, hright, hrightEq⟩ := List.mem_map.mp hmemRaw'
    by_cases heq : left = right
    · have hleftName : left.name = name := congrArg Prod.fst hleftEq
      have hrightName : right.name = name' := congrArg Prod.fst hrightEq
      exact hleftName.symm.trans ((congrArg CalleeParameter.name heq).trans hrightName)
    · have hleftDisj := hrel left hleft right hright heq
      obtain ⟨slot, hslot, hslot'⟩ := hcommon
      have hslotLeft : left.slots = slots :=
        congrArg Prod.snd (congrArg Prod.snd hleftEq)
      have hslotRight : right.slots = slots' :=
        congrArg Prod.snd (congrArg Prod.snd hrightEq)
      exfalso
      apply hleftDisj slot
      · rw [hslotLeft]
        exact hslot
      · rw [hslotRight]
        exact hslot'

/-! The corresponding `ctxt_max` fact uses Cake's inclusive maximum: the
    compiler's next-free slot minus one bounds every parameter slot. -/
theorem panValueCtxtMax_compileParamVars
    [LawfulBEq String]
    (params : List (VarName × Shape)) (offset : Nat)
    (hnames : (params.map Prod.fst).Nodup) :
    panValueCtxtMax
      ((compileParamVars params offset).2.2 - 1)
      ((compileParamVars params offset).1.reverse) := by
  have hnamesCompiled :
      ((compileParamVars params offset).1.map Prod.fst).Nodup := by
    have hshapes := compileParamVars_preserves_parameter_shapes params offset
    have hnames' := congrArg (List.map Prod.fst) hshapes
    have heq :
        (compileParamVars params offset).1.map Prod.fst = params.map Prod.fst := by
      simpa [Function.comp_def] using hnames'
    rw [heq]
    exact hnames
  refine ⟨by omega, ?_⟩
  intro name shape slots hlookup slot hslot
  have hlookupRaw : lookupInfo name (compileParamVars params offset).1 =
      some (shape, slots) := by
    rw [← lookupInfo_reverse_of_nodup name
      (compileParamVars params offset).1 hnamesCompiled] at hlookup
    exact hlookup
  have hlt := compileParamVars_slot_lt params offset name shape slots
    hlookupRaw slot hslot
  omega
/-! Package the two Cake context invariants for the compiler-generated
    parameter map.  This is the concrete `mk_ctxt` fragment used when a
    source callee is entered with its flattened parameters. -/
theorem panToCrepMakeVmap_context_invariants
    [LawfulBEq String]
    (params : List (VarName × Shape))
    (hnames : (params.map Prod.fst).Nodup) :
    panValueNoOverlap (panToCrepMakeVmap params) ∧
      panValueCtxtMax
        ((compileParamVars params 0).2.2 - 1)
        (panToCrepMakeVmap params) := by
  constructor
  · simpa [panToCrepMakeVmap] using
      panValueNoOverlap_compileParamVars params 0
  · simpa [panToCrepMakeVmap] using
      panValueCtxtMax_compileParamVars params 0 hnames

/-! Cake's `state_rel` packages `locals_rel`, whose defining premises are
    `no_overlap` and `ctxt_max`, together with the source-global and memory
    components.  The existing `panValueCrepStateRel` is intentionally kept
    as the compatibility relation used by the lower-level correctness files;
    this strengthened wrapper exposes the original invariant shape for the
    top-level `state_rel_imp_semantics_to_crep` port. -/
def panValueCrepStateRelWithContext [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepState : CrepState α) : Prop :=
  panValueNoOverlap context.vars ∧
    panValueCtxtMax context.maxVar context.vars ∧
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory crepState

theorem panValueCrepStateRelWithContext_to_stateRel [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepState : CrepState α)
    (hrel : panValueCrepStateRelWithContext structs context sourceLocals
      sourceGlobals sourceMemory crepState) :
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory crepState :=
  hrel.2.2

theorem panValueCrepStateRelWithContext_of_stateRel [BEq String]
    (structs : StructContext) (context : CompileContext α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (crepState : CrepState α)
    (hoverlap : panValueNoOverlap context.vars)
    (hmax : panValueCtxtMax context.maxVar context.vars)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory crepState) :
    panValueCrepStateRelWithContext structs context sourceLocals sourceGlobals
      sourceMemory crepState :=
  ⟨hoverlap, hmax, hrel⟩
def panValuePcLocalisedCode (code : PanValuePcSourceCode α) : Prop :=
  ∀ entry ∈ code, localisedProg entry.2.2

/-- Cake `code_rel_imp` analogue: a localised source table exposes localisation
for every looked-up function body. -/
theorem panValuePcLocalisedCode_lookup [LawfulBEq String]
    {code : PanValuePcSourceCode α} (h : panValuePcLocalisedCode code) :
    ∀ name parameters body,
      lookupPanFunction name code = some (parameters, body) →
      localisedProg body :=
  fun name parameters body hlookup =>
    h (name, parameters, body) (lookupPanFunction_mem hlookup)

/-! The exception clause of HOL `pc_compile_correct`: the target exception is
the code looked up for the source exception, and a non-empty payload is
available through `globalsLookup` with the same flattening and 32-word bound.
The lookup functions are parameters because the current Lean state relation
still models only the empty source-global boundary. -/
def panValuePcExceptionResultRel
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α) : Prop :=
  ∃ spillAddress code,
    exceptionCode sourceException = some code ∧
    targetException = code ∧
    panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory sourceException sourceValue targetState
      targetException spillAddress ∧
    (1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue = some (panValueFlatWords sourceValue) ∧
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)

/-! Exact Cake exception-code provenance for the raised result clause.  The
    compatibility relation above keeps the historical result-code adapter
    usable, but Cake's `pc_compile_correct` does not permit an unrelated code
    map: its target code is `FLOOKUP ctxt.eids eid`.  This strengthened
    relation makes that missing premise explicit at the boundary. -/
def panValuePcExceptionResultRelWithContextCode
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α) : Prop :=
  panValuePcExceptionResultRel structs context exceptionRel exceptionCode
    globalsLookup sourceGlobals sourceMemory sourceException sourceValue
    targetState targetException ∧
  lookupInfo sourceException context.exceptions = some targetException

/-! The explicit state/global/memory result relation.  The raised branch uses
the compiler-owned spill relation already used by the downstream Crep
correctness lemmas; timeout and FinalFFI retain the ordinary state relation. -/
def panValuePcResultRel
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    : PanValuePcResult α → CrepPcResult α → Prop
  | .error, _ => False
  | .normal sourceLocals sourceGlobals sourceMemory,
      .normal targetState =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState
  | .returned sourceLocals sourceGlobals sourceMemory sourceValues,
      .returned targetState targetValues =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValueCrepValuesRel sourceValues targetValues
  | .raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue,
      .raised targetState targetException =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRel structs context exceptionRel exceptionCode
        globalsLookup sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException
  | .broke sourceLocals sourceGlobals sourceMemory, .broke targetState 0 =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState
  | .continued sourceLocals sourceGlobals sourceMemory, .continued targetState 0 =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState
  | .timeout sourceLocals sourceGlobals sourceMemory, .timeout targetState =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState
  | .finalFfi sourceLocals sourceGlobals sourceMemory sourceEvent,
      .finalFfi targetState targetEvent =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧ sourceEvent = targetEvent
  | _, _ => False

def panValuePcResultRelWithContextCode
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α)) :
    PanValuePcResult α → CrepPcResult α → Prop
  | .raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue,
      .raised targetState targetException =>
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException
  | sourceResult, targetResult =>
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        sourceResult targetResult

/-! The source compiler-correctness theorem only permits the loop-control
label `0` at this boundary.  Keep these rejection lemmas next to the
relation so a future broadening of the pattern cannot silently weaken the
statement back to an arbitrary target label. -/
theorem panValuePcResultRel_broke_rejects_nonzero_label
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α)
    (label : Nat) (hlabel : label ≠ 0) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (.broke sourceLocals sourceGlobals sourceMemory)
      (.broke targetState label) := by
  simp [panValuePcResultRel, hlabel]

theorem panValuePcResultRel_continued_rejects_nonzero_label
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α)
    (label : Nat) (hlabel : label ≠ 0) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (.continued sourceLocals sourceGlobals sourceMemory)
      (.continued targetState label) := by
  simp [panValuePcResultRel, hlabel]

/-! HOL `pc_compile_correct` excludes the source `Error` case by a premise,
and the relation never relates it.  Record the remaining excluded
constructor pairs explicitly so a future broadening of the match cannot
silently admit an unreachable combination. -/
theorem panValuePcResultRel_rejects_source_error
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetResult : CrepPcResult α) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup PanValuePcResult.error targetResult := by
  cases targetResult <;> simp [panValuePcResultRel]

theorem panValuePcResultRel_rejects_target_error
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceResult : PanValuePcResult α) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup sourceResult CrepPcResult.error := by
  cases sourceResult <;> simp [panValuePcResultRel]

theorem panValuePcResultRel_rejects_normal_returned
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α)
    (targetValues : List α) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (.normal sourceLocals sourceGlobals sourceMemory)
      (.returned targetState targetValues) := by
  simp [panValuePcResultRel]

theorem panValuePcResultRel_rejects_broke_continued
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α)
    (label : Nat) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (.broke sourceLocals sourceGlobals sourceMemory)
      (.continued targetState label) := by
  simp [panValuePcResultRel]

theorem panValuePcResultRel_rejects_timeout_normal
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (.timeout sourceLocals sourceGlobals sourceMemory)
      (.normal targetState) := by
  simp [panValuePcResultRel]

theorem panValuePcResultRel_rejects_finalFfi_normal
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceEvent : FfiFinalEvent)
    (targetState : CrepState α) :
    ¬ panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (.finalFfi sourceLocals sourceGlobals sourceMemory sourceEvent)
      (.normal targetState) := by
  simp [panValuePcResultRel]

/-- The concrete rejection lemmas above are instances of a single
constructor-agreement invariant: whenever `panValuePcResultRel` holds, the
source and target results are observations of the same outcome constructor.
Recording the invariant makes the set of excluded pairs exhaustive rather
than a hand-maintained list. -/
def panValuePcResultConstructor : PanValuePcResult α → Nat
  | .error => 0
  | .normal .. => 1
  | .returned .. => 2
  | .raised .. => 3
  | .broke .. => 4
  | .continued .. => 5
  | .timeout .. => 6
  | .finalFfi .. => 7

def crepPcResultConstructor : CrepPcResult α → Nat
  | .error => 0
  | .normal .. => 1
  | .returned .. => 2
  | .raised .. => 3
  | .broke .. => 4
  | .continued .. => 5
  | .timeout .. => 6
  | .finalFfi .. => 7

theorem panValuePcResultRel_constructor_eq
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceResult : PanValuePcResult α) (targetResult : CrepPcResult α)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup sourceResult targetResult) :
    panValuePcResultConstructor sourceResult =
      crepPcResultConstructor targetResult := by
  cases sourceResult <;> cases targetResult <;>
    simp_all [panValuePcResultRel, panValuePcResultConstructor,
      crepPcResultConstructor]

/-! Constructor inversion lemmas for the result relation.  Each exposes the
exact state/global/memory obligation of one reachable result pair, so
downstream composition can rewrite instead of re-unfolding the definition. -/
theorem panValuePcResultRel_normal_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal targetState) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  simp [panValuePcResultRel]

theorem panValuePcResultRel_returned_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceValues : List (PanValue α))
    (targetState : CrepState α) (targetValues : List α) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.returned sourceLocals sourceGlobals sourceMemory sourceValues)
      (.returned targetState targetValues) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValueCrepValuesRel sourceValues targetValues := by
  simp [panValuePcResultRel]

theorem panValuePcResultRel_broke_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.broke sourceLocals sourceGlobals sourceMemory) (.broke targetState 0) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  simp [panValuePcResultRel]

theorem panValuePcResultRel_continued_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.continued sourceLocals sourceGlobals sourceMemory)
      (.continued targetState 0) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  simp [panValuePcResultRel]

theorem panValuePcResultRel_timeout_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.timeout sourceLocals sourceGlobals sourceMemory) (.timeout targetState) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  simp [panValuePcResultRel]

theorem panValuePcResultRel_finalFfi_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceEvent : FfiFinalEvent)
    (targetState : CrepState α) (targetEvent : FfiFinalEvent) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.finalFfi sourceLocals sourceGlobals sourceMemory sourceEvent)
      (.finalFfi targetState targetEvent) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧ sourceEvent = targetEvent := by
  simp [panValuePcResultRel]

theorem panValuePcResultRel_raised_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRel structs context exceptionRel exceptionCode
        globalsLookup sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException := by
  simp [panValuePcResultRel]

theorem panValuePcResultRelWithContextCode_raised_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException := by
  simp [panValuePcResultRelWithContextCode]

theorem panValuePcResultRelWithContextCode_normal_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal targetState) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  simp [panValuePcResultRelWithContextCode, panValuePcResultRel]

theorem panValuePcResultRelWithContextCode_returned_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceValues : List (PanValue α))
    (targetState : CrepState α) (targetValues : List α) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.returned sourceLocals sourceGlobals sourceMemory sourceValues)
      (.returned targetState targetValues) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValueCrepValuesRel sourceValues targetValues := by
  simp [panValuePcResultRelWithContextCode, panValuePcResultRel]

theorem panValuePcResultRelWithContextCode_broke_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.broke sourceLocals sourceGlobals sourceMemory) (.broke targetState 0) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  simp [panValuePcResultRelWithContextCode, panValuePcResultRel]

theorem panValuePcResultRelWithContextCode_continued_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.continued sourceLocals sourceGlobals sourceMemory)
      (.continued targetState 0) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  simp [panValuePcResultRelWithContextCode, panValuePcResultRel]

theorem panValuePcResultRelWithContextCode_timeout_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.timeout sourceLocals sourceGlobals sourceMemory) (.timeout targetState) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState := by
  simp [panValuePcResultRelWithContextCode, panValuePcResultRel]

theorem panValuePcResultRelWithContextCode_finalFfi_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceEvent : FfiFinalEvent)
    (targetState : CrepState α) (targetEvent : FfiFinalEvent) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.finalFfi sourceLocals sourceGlobals sourceMemory sourceEvent)
      (.finalFfi targetState targetEvent) ↔
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧ sourceEvent = targetEvent := by
  simp [panValuePcResultRelWithContextCode, panValuePcResultRel]

theorem panValuePcExceptionResultRelWithContextCode_of_rel_and_lookup
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α)
    (h : panValuePcExceptionResultRel structs context exceptionRel exceptionCode
      globalsLookup sourceGlobals sourceMemory sourceException sourceValue
      targetState targetException)
    (hlookup : lookupInfo sourceException context.exceptions = some targetException) :
    panValuePcExceptionResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
      sourceValue targetState targetException :=
  ⟨h, hlookup⟩

theorem panValuePcResultRelWithContextCode_raised_of_rel_and_lookup
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α)
    (h : panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException))
    (hlookup : lookupInfo sourceException context.exceptions = some targetException) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) := by
  simp only [panValuePcResultRelWithContextCode, panValuePcResultRel,
    panValuePcExceptionResultRelWithContextCode] at h ⊢
  exact ⟨h.1, h.2, hlookup⟩

theorem panValuePcResultRelWithContextCode_broke_rejects_nonzero_label
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α)
    (label : Nat) (hlabel : label ≠ 0) :
    ¬ panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup
      (.broke sourceLocals sourceGlobals sourceMemory)
      (.broke targetState label) := by
  simp [panValuePcResultRelWithContextCode, panValuePcResultRel, hlabel]

theorem panValuePcResultRelWithContextCode_continued_rejects_nonzero_label
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α)
    (label : Nat) (hlabel : label ≠ 0) :
    ¬ panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup
      (.continued sourceLocals sourceGlobals sourceMemory)
      (.continued targetState label) := by
  simp [panValuePcResultRelWithContextCode, panValuePcResultRel, hlabel]

/-- The context-coded relation agrees with the plain relation on every pair
except `raised`/`raised`, so the constructor-agreement invariant transfers. -/
theorem panValuePcResultRelWithContextCode_constructor_eq
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceResult : PanValuePcResult α) (targetResult : CrepPcResult α)
    (hrel : panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup sourceResult targetResult) :
    panValuePcResultConstructor sourceResult =
      crepPcResultConstructor targetResult := by
  cases sourceResult <;> cases targetResult <;>
    simp_all [panValuePcResultRelWithContextCode, panValuePcResultRel,
      panValuePcResultConstructor, crepPcResultConstructor]

theorem panValuePcResultRelWithContextCode_rejects_source_error
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (targetResult : CrepPcResult α) :
    ¬ panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup PanValuePcResult.error targetResult := by
  cases targetResult <;> simp [panValuePcResultRelWithContextCode,
    panValuePcResultRel]

theorem panValuePcResultRelWithContextCode_rejects_target_error
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceResult : PanValuePcResult α) :
    ¬ panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup sourceResult CrepPcResult.error := by
  cases sourceResult <;> simp [panValuePcResultRelWithContextCode,
    panValuePcResultRel]

/-! Safety obligation for the compact `pc_compile_correct` bridge.  The
intermediate control relation intentionally permits nonzero labels while a
loop propagates them, but the final Pancake theorem only admits label `0` for
the result exposed at its boundary. -/
def panValuePcControlLabelSafe
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α) : Prop :=
  match sourceResult, crepResult with
  | .broke _ _ _, .broke _ label => label = 0
  | .continued _ _ _, .continued _ label => label = 0
  | _, _ => True

def PanValueCrepProgramStateControlSafe
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (_exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α),
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state →
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory program = some sourceResult →
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (compileProg context program) = some crepResult →
    panValuePcControlLabelSafe sourceResult crepResult

/-! The stateful evaluator proof and the final Pc boundary proof require two
independent facts about every program: its source/Crep state simulation and
the fact that a top-level `break`/`continue` carries label zero.  Keeping
these facts paired is important for sequencing: the safety proof for the
first component needs its state-correctness proof in order to expose the
intermediate result.  This is the direct induction assembly for that paired
obligation, including handlers hidden in call metadata. -/
theorem panValueCrepProgramStateCorrect_and_controlSafe_induction
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (hskip : PanValueCrepProgramStateCorrect (.skip : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.skip : Prog α))
    (hdec : ∀ (name : VarName) (shape : Shape) (value : Exp α)
      (body : Prog α),
      (PanValueCrepProgramStateCorrect body ∧
        PanValueCrepProgramStateControlSafe body) →
      PanValueCrepProgramStateCorrect (.dec name shape value body) ∧
        PanValueCrepProgramStateControlSafe (.dec name shape value body))
    (hassign : ∀ (kind : VarKind) (name : VarName) (value : Exp α),
      PanValueCrepProgramStateCorrect (.assign kind name value) ∧
        PanValueCrepProgramStateControlSafe (.assign kind name value))
    (hprimitive : ∀ (name : VarName) (operator : PrimOp)
      (args : List (Exp α)),
      PanValueCrepProgramStateCorrect (.primitive name operator args) ∧
        PanValueCrepProgramStateControlSafe (.primitive name operator args))
    (hstore : ∀ (address value : Exp α),
      PanValueCrepProgramStateCorrect (.store address value) ∧
        PanValueCrepProgramStateControlSafe (.store address value))
    (hstore32 : ∀ (address value : Exp α),
      PanValueCrepProgramStateCorrect (.store32 address value) ∧
        PanValueCrepProgramStateControlSafe (.store32 address value))
    (hstoreByte : ∀ (address value : Exp α),
      PanValueCrepProgramStateCorrect (.storeByte address value) ∧
        PanValueCrepProgramStateControlSafe (.storeByte address value))
    (hseq : ∀ (first second : Prog α),
      (PanValueCrepProgramStateCorrect first ∧
        PanValueCrepProgramStateControlSafe first) →
      (PanValueCrepProgramStateCorrect second ∧
        PanValueCrepProgramStateControlSafe second) →
      PanValueCrepProgramStateCorrect (.seq first second) ∧
        PanValueCrepProgramStateControlSafe (.seq first second))
    (hite : ∀ (condition : Exp α) (thenBranch elseBranch : Prog α),
      (PanValueCrepProgramStateCorrect thenBranch ∧
        PanValueCrepProgramStateControlSafe thenBranch) →
      (PanValueCrepProgramStateCorrect elseBranch ∧
        PanValueCrepProgramStateControlSafe elseBranch) →
      PanValueCrepProgramStateCorrect (.ite condition thenBranch elseBranch) ∧
        PanValueCrepProgramStateControlSafe (.ite condition thenBranch elseBranch))
    (hwhile : ∀ (condition : Exp α) (body : Prog α),
      (PanValueCrepProgramStateCorrect body ∧
        PanValueCrepProgramStateControlSafe body) →
      PanValueCrepProgramStateCorrect (.while condition body) ∧
        PanValueCrepProgramStateControlSafe (.while condition body))
    (hbreak : PanValueCrepProgramStateCorrect (.break : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.break : Prog α))
    (hcontinue : PanValueCrepProgramStateCorrect (.continue : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.continue : Prog α))
    (hcall : ∀
      (info : Option (Option (VarKind × VarName) ×
        Option (ExceptionId × VarName × Prog α)))
      (name : FunName) (args : List (Exp α)),
      (match info with
       | some (_, some (_, _, handler)) =>
           PanValueCrepProgramStateCorrect handler ∧
             PanValueCrepProgramStateControlSafe handler
       | _ => True) →
      PanValueCrepProgramStateCorrect (.call info name args) ∧
        PanValueCrepProgramStateControlSafe (.call info name args))
    (hdecCall : ∀ (name : VarName) (shape : Shape) (function : FunName)
      (args : List (Exp α)) (body : Prog α),
      (PanValueCrepProgramStateCorrect body ∧
        PanValueCrepProgramStateControlSafe body) →
      PanValueCrepProgramStateCorrect (.decCall name shape function args body) ∧
        PanValueCrepProgramStateControlSafe (.decCall name shape function args body))
    (hextCall : ∀ (function : FunName)
      (configuration configurationLength array arrayLength : Exp α),
      PanValueCrepProgramStateCorrect
          (.extCall function configuration configurationLength array arrayLength) ∧
        PanValueCrepProgramStateControlSafe
          (.extCall function configuration configurationLength array arrayLength))
    (hraise : ∀ (exception : ExceptionId) (value : Exp α),
      PanValueCrepProgramStateCorrect (.raise exception value) ∧
        PanValueCrepProgramStateControlSafe (.raise exception value))
    (hreturn : ∀ (value : Exp α),
      PanValueCrepProgramStateCorrect (.return value) ∧
        PanValueCrepProgramStateControlSafe (.return value))
    (hshMemLoad : ∀ (size : OpSize) (kind : VarKind) (name : VarName)
      (address : Exp α),
      PanValueCrepProgramStateCorrect (.shMemLoad size kind name address) ∧
        PanValueCrepProgramStateControlSafe (.shMemLoad size kind name address))
    (hshMemStore : ∀ (size : OpSize) (address value : Exp α),
      PanValueCrepProgramStateCorrect (.shMemStore size address value) ∧
        PanValueCrepProgramStateControlSafe (.shMemStore size address value))
    (htick : PanValueCrepProgramStateCorrect (.tick : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.tick : Prog α))
    (hannot : ∀ (tag text : String),
      PanValueCrepProgramStateCorrect (@Prog.annot α tag text) ∧
        PanValueCrepProgramStateControlSafe (@Prog.annot α tag text)) :
    ∀ program : Prog α,
      PanValueCrepProgramStateCorrect program ∧
        PanValueCrepProgramStateControlSafe program := by
  let rec go : (program : Prog α) →
      PanValueCrepProgramStateCorrect program ∧
        PanValueCrepProgramStateControlSafe program
    | .skip => hskip
    | .dec name shape value body => hdec name shape value body (go body)
    | .assign kind name value => hassign kind name value
    | .primitive name operator args => hprimitive name operator args
    | .store address value => hstore address value
    | .store32 address value => hstore32 address value
    | .storeByte address value => hstoreByte address value
    | .seq first second => hseq first second (go first) (go second)
    | .ite condition thenBranch elseBranch =>
        hite condition thenBranch elseBranch (go thenBranch) (go elseBranch)
    | .while condition body => hwhile condition body (go body)
    | .break => hbreak
    | .continue => hcontinue
    | .call info name args =>
        hcall info name args (by
          cases info with
          | none => exact True.intro
          | some info =>
              cases info with
              | mk destination handlerInfo =>
                  cases handlerInfo with
                  | none => exact True.intro
                  | some handler =>
                      cases handler with
                      | mk exception handlerInfo =>
                          cases handlerInfo with
                          | mk handlerVar handlerProgram =>
                              exact go handlerProgram)
    | .decCall name shape function args body =>
        hdecCall name shape function args body (go body)
    | .extCall function configuration configurationLength array arrayLength =>
        hextCall function configuration configurationLength array arrayLength
    | .raise exception value => hraise exception value
    | .return value => hreturn value
    | .shMemLoad size kind name address => hshMemLoad size kind name address
    | .shMemStore size address value => hshMemStore size address value
    | .tick => htick
    | .annot tag text => hannot tag text
    termination_by program => sizeOf program
  exact fun program => go program

/-! The two primitive loop-control constructors already produce label `0` in
the source and stateful Crep evaluators.  These leaf proofs discharge the
first concrete instances of the safety premise required by the Pc bridge. -/
theorem panValueCrepProgramStateControlSafe_break
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateControlSafe (.break : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProgState] at hsource hcrep
          cases hsource
          cases hcrep
          rfl

/-! A call without an exception handler never produces a source-level
`break`/`continue` outcome: the source call evaluator maps the callee's
`normal`/`broke`/`continued` results to `none` and only a caught-handler
program can propagate them.  Hence the control-label obligation is
immediate for the handler-free call forms, which is the first concrete
call instance of the safety premise used by the compact Pc bridge. -/
theorem panValueCrepProgramStateControlSafe_call_none
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : FunName) (args : List (Exp α)) :
    PanValueCrepProgramStateControlSafe (.call none name args) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases sourceFuel with
      | zero =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi,
            evalPanValueCallWithPrimitiveCallsAndFfi] at hsource
      | succ sourceFuel =>
          simp only [evalPanValueProgWithPrimitiveCallsAndFfi,
            evalPanValueCallWithPrimitiveCallsAndFfi] at hsource
          cases hvalues : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord args with
          | none => simp [hvalues, Option.bind_eq_bind, Option.bind_none] at hsource
          | some values =>
              cases hlookup : lookupPanFunction name sourceFunctions with
              | none =>
                  simp [hvalues, hlookup, Option.bind_eq_bind, Option.bind_none] at hsource
              | some pair =>
                  obtain ⟨parameters, body⟩ := pair
                  by_cases hparams : panValueParametersValid structs none name values = true
                  · simp only [hvalues, hlookup, hparams, if_true, Option.bind_eq_bind,
                      Option.bind_some] at hsource
                    cases hbind : bindPanValueParameters parameters values with
                    | none =>
                        simp [hbind, Option.bind_none] at hsource
                    | some calleeLocals =>
                        simp only [hbind, Option.bind_some] at hsource
                        cases hcallee : evalPanValueProgWithPrimitiveCallsAndFfi primitive
                          sourceHandler structs sourceFunctions baseAddress topAddress bytesInWord
                          sourceFuel calleeLocals sourceGlobals sourceMemory body with
                        | none => simp [hcallee] at hsource
                        | some calleeResult =>
                            cases calleeResult with
                            | normal locals globals memory => simp [hcallee] at hsource
                            | broke locals globals memory => simp [hcallee] at hsource
                            | continued locals globals memory => simp [hcallee] at hsource
                            | returned locals calleeGlobals calleeMemory values =>
                                by_cases hret : (panValueReturnValid structs none name values &&
                                    panValueValuesWithinLimit structs values) = true
                                · simp only [hcallee, Option.bind_some,
                                    hret, if_true, Option.pure_def, Option.some.injEq] at hsource
                                  subst sourceResult
                                  simp [panValuePcControlLabelSafe]
                                · simp only [hcallee, Option.bind_some] at hsource
                                  rw [if_neg hret] at hsource
                                  simp at hsource
                            | raised locals calleeGlobals calleeMemory exception value =>
                                by_cases hexc : (panValueExceptionValid structs none exception value &&
                                    panValuePayloadWithinLimit structs value) = true
                                · simp only [hcallee, Option.bind_some,
                                    hexc, if_true, Option.pure_def, Option.some.injEq] at hsource
                                  subst sourceResult
                                  simp [panValuePcControlLabelSafe]
                                · simp only [hcallee, Option.bind_some] at hsource
                                  rw [if_neg hexc] at hsource
                                  simp at hsource
                  · simp only [hvalues, hlookup, Option.bind_eq_bind, Option.bind_some] at hsource
                    rw [if_neg hparams] at hsource
                    simp at hsource

/-- The handler-free call with a return destination also cannot propagate a
source-level `break`/`continue`: the returned branch materialises a `normal`
result through `assignPanValueCallResult`. -/
theorem panValueCrepProgramStateControlSafe_call_returns
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (destination : Option (VarKind × VarName)) (name : FunName)
    (args : List (Exp α)) :
    PanValueCrepProgramStateControlSafe (.call (some (destination, none)) name args) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases sourceFuel with
      | zero =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi,
            evalPanValueCallWithPrimitiveCallsAndFfi] at hsource
      | succ sourceFuel =>
          simp only [evalPanValueProgWithPrimitiveCallsAndFfi,
            evalPanValueCallWithPrimitiveCallsAndFfi] at hsource
          cases hvalues : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord args with
          | none => simp [hvalues, Option.bind_none] at hsource
          | some values =>
              cases hlookup : lookupPanFunction name sourceFunctions with
              | none =>
                  simp [hvalues, hlookup, Option.bind_none] at hsource
              | some pair =>
                  obtain ⟨parameters, body⟩ := pair
                  by_cases hparams : panValueParametersValid structs none name values = true
                  · simp only [hvalues, hlookup, hparams, if_true,
                      Option.bind_eq_bind,
                      Option.bind_some] at hsource
                    cases hbind : bindPanValueParameters parameters values with
                    | none =>
                        simp [hbind, Option.bind_none] at hsource
                    | some calleeLocals =>
                        simp only [hbind, Option.bind_some] at hsource
                        cases hcallee : evalPanValueProgWithPrimitiveCallsAndFfi primitive
                          sourceHandler structs sourceFunctions baseAddress topAddress bytesInWord
                          sourceFuel calleeLocals sourceGlobals sourceMemory body with
                        | none => simp [hcallee] at hsource
                        | some calleeResult =>
                            cases calleeResult with
                            | normal locals globals memory => simp [hcallee] at hsource
                            | broke locals globals memory => simp [hcallee] at hsource
                            | continued locals globals memory => simp [hcallee] at hsource
                            | returned locals calleeGlobals calleeMemory values =>
                                by_cases hret : (panValueReturnValid structs none name values &&
                                    panValueValuesWithinLimit structs values) = true
                                · simp only [hcallee, Option.bind_some,
                                    hret, if_true, Option.pure_def] at hsource
                                  cases hassign : assignPanValueCallResult sourceLocals calleeGlobals
                                    destination values (structs := structs) with
                                  | none =>
                                      simp [hassign,
                                        Option.bind_none] at hsource
                                  | some assigned =>
                                      obtain ⟨assignedLocals, assignedGlobals⟩ := assigned
                                      simp only [hassign, Option.bind_some,
                                        Option.some.injEq] at hsource
                                      subst sourceResult
                                      simp [panValuePcControlLabelSafe]
                                · simp only [hcallee, Option.bind_some] at hsource
                                  rw [if_neg hret] at hsource
                                  simp at hsource
                            | raised locals calleeGlobals calleeMemory exception value =>
                                by_cases hexc : (panValueExceptionValid structs none exception value &&
                                    panValuePayloadWithinLimit structs value) = true
                                · simp only [hcallee, Option.bind_some,
                                    hexc, if_true, Option.pure_def, Option.some.injEq] at hsource
                                  subst sourceResult
                                  simp [panValuePcControlLabelSafe]
                                · simp only [hcallee, Option.bind_some] at hsource
                                  rw [if_neg hexc] at hsource
                                  simp at hsource
                  · simp only [hvalues, hlookup, Option.bind_eq_bind, Option.bind_some] at hsource
                    rw [if_neg hparams] at hsource
                    simp at hsource

theorem panValueCrepProgramStateControlSafe_continue
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateControlSafe (.continue : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProgState] at hsource hcrep
          cases hsource
          cases hcrep
          rfl

theorem panValueCrepProgramStateControlSafe_skip
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateControlSafe (.skip : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProgState] at hsource hcrep
          cases hsource
          simp [panValuePcControlLabelSafe]

theorem panValueCrepProgramStateControlSafe_tick
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateControlSafe (.tick : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProgState] at hsource hcrep
          cases hsource
          simp [panValuePcControlLabelSafe]

theorem panValueCrepProgramStateControlSafe_annot
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (tag text : String) :
    PanValueCrepProgramStateControlSafe (@Prog.annot α tag text) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProgState] at hsource hcrep
          cases hsource
          simp [panValuePcControlLabelSafe]

theorem panValueCrepProgramStateControlSafe_return_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (value : α) :
    PanValueCrepProgramStateControlSafe
      (.return (.const value) : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          have hlimit : panValuePayloadWithinLimit structs (.word value) = true :=
            panValuePayloadWithinLimit_word structs value
          have hsourceResult :
              PanValueControlResult.returned (fun _ => none) sourceGlobals
                sourceMemory [.word value] = sourceResult := by
            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
              evalPanValueExp, hlimit] using hsource
          have hcrepResult :
              CrepControlResult.returned state [value] = crepResult := by
            simpa [compileProg, compileExp, evalCrepFullProgState,
              evalCrepFullExpsState, evalCrepFullExpState] using hcrep
          cases hsourceResult
          cases hcrepResult
          simp [panValuePcControlLabelSafe]

theorem panValueCrepProgramStateControlSafe_raise
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (expression : Exp α) :
    PanValueCrepProgramStateControlSafe (.raise exception expression) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord expression with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
      | some value =>
          cases hvalid : panValuePayloadWithinLimit structs value with
          | false =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid]
                at hsource
          | true =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue, hvalid]
                at hsource
              cases hsource
              simp [panValuePcControlLabelSafe]

theorem panValueCrepProgramStateControlSafe_store
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : Exp α) :
    PanValueCrepProgramStateControlSafe (.store address value) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases haddress : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord address with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at hsource
      | some addressValue =>
          cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord value with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hvalue]
                at hsource
          | some storedValue =>
              cases addressValue with
              | word word =>
                  cases hstore : panValueStoreWithAccess sourceMemory
                      bytesInWord word storedValue with
                  | none =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue, hstore] at hsource
                  | some memory =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue, hstore] at hsource
                      cases hsource
                      simp [panValuePcControlLabelSafe]
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at hsource
              | nStruct name fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at hsource

theorem panValueCrepProgramStateControlSafe_store32
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : Exp α) :
    PanValueCrepProgramStateControlSafe (.store32 address value) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases haddress : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord address with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at hsource
      | some addressValue =>
          cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord value with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hvalue]
                at hsource
          | some storedValue =>
              cases addressValue with
              | word word =>
                  cases storedValue with
                  | word wordValue =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at hsource
                      cases hsource
                      simp [panValuePcControlLabelSafe]
                  | rStruct fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at hsource
                  | nStruct name fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at hsource
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at hsource
              | nStruct name fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at hsource

theorem panValueCrepProgramStateControlSafe_storeByte
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : Exp α) :
    PanValueCrepProgramStateControlSafe (.storeByte address value) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hstate hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases haddress : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord address with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress] at hsource
      | some addressValue =>
          cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord value with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress, hvalue]
                at hsource
          | some storedValue =>
              cases addressValue with
              | word word =>
                  cases storedValue with
                  | word wordValue =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at hsource
                      cases hsource
                      simp [panValuePcControlLabelSafe]
                  | rStruct fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at hsource
                  | nStruct name fields =>
                      simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                        hvalue] at hsource
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at hsource
              | nStruct name fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, haddress,
                    hvalue] at hsource

/-! The store family's paired source-word bridges, mirroring the return/ite/
while bridges: the state-correctness half is the generic word-store theorem
and the control half is the label rule, with `hlookup`/`hstable` explicit. -/
theorem panValueCrepProgramStateCorrect_and_controlSafe_store_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstable : ∀ (state : CrepState α) (baseAddress topAddress : α)
      (temporary : Nat) (compiled : CrepExp α) (value updateValue : α),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value) :
    PanValueCrepProgramStateCorrect (.store address.toExp value.toExp) ∧
      PanValueCrepProgramStateControlSafe (.store address.toExp value.toExp) := by
  constructor
  · exact panValueCrepProgramStateCorrect_store_source_word address value
      hbytesInWord hlookup hstable
  · exact panValueCrepProgramStateControlSafe_store address.toExp value.toExp

theorem panValueCrepProgramStateCorrect_and_controlSafe_store32_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect (.store32 address.toExp value.toExp) ∧
      PanValueCrepProgramStateControlSafe (.store32 address.toExp value.toExp) := by
  constructor
  · exact panValueCrepProgramStateCorrect_store32_source_word address value
      hbytesInWord hlookup
  · exact panValueCrepProgramStateControlSafe_store32 address.toExp value.toExp

theorem panValueCrepProgramStateCorrect_and_controlSafe_storeByte_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect (.storeByte address.toExp value.toExp) ∧
      PanValueCrepProgramStateControlSafe (.storeByte address.toExp value.toExp) := by
  constructor
  · exact panValueCrepProgramStateCorrect_storeByte_source_word address value
      hbytesInWord hlookup
  · exact panValueCrepProgramStateControlSafe_storeByte address.toExp value.toExp

/-! Cake's `pc_compile_correct[Raise]` case (`pan_to_crepProofScript.sml:
1957-2054`) raises a flattened word value and never exposes loop control.  This
bridge supplies the missing control half for the existing source-word raise
state theorem. -/
theorem panValueCrepProgramStateCorrect_and_controlSafe_raise_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (expression : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (value exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.word value) exceptionCode) :
    PanValueCrepProgramStateCorrect (.raise exception expression.toExp) ∧
      PanValueCrepProgramStateControlSafe (.raise exception expression.toExp) := by
  constructor
  · exact panValueCrepProgramStateCorrect_raise_source_word exception expression
      hbytesInWord hlookup hlookupException hfresh hexception
  · exact panValueCrepProgramStateControlSafe_raise exception expression.toExp

/-! Cake's `pc_compile_correct[Return]` case (`pan_to_crepProofScript.sml:
2056-2070`) returns a flattened value and never exposes loop control.  This
bridge supplies the missing control half for the existing source-word return
state theorem. -/
theorem panValueCrepProgramStateControlSafe_return_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateControlSafe (.return expression.toExp) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hvalue : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord expression.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, hvalue] at hsource
      | some sourceValue' =>
          obtain ⟨value, hword⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun name value hvalue =>
              hlookup context sourceLocals name value hvalue)
            expression sourceValue' hvalue
          have hsourceValue :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord expression.toExp =
                some (.word value) := by
            rw [hvalue, hword]
          have hsourceExpected :
              evalPanValueProgWithPrimitiveCallsAndFfi
                primitive sourceHandler structs sourceFunctions
                baseAddress topAddress bytesInWord (sourceFuel + 1)
                sourceLocals sourceGlobals sourceMemory
                (.return expression.toExp) =
                some (.returned (fun _ => none) sourceGlobals sourceMemory
                  [.word value]) := by
            simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceValue]
          cases targetFuel with
          | zero =>
              simp [evalCrepFullProgState] at hcrep
          | succ targetFuel =>
              obtain ⟨_compiled, _hcompile, _hcompiled, _, hcrepExpected,
                _hrelation⟩ :=
                compile_full_pan_value_return_source_word_state_relation_fuel
                  context structs sourceFunctions functions sourceLocals sourceGlobals
                  sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
                  baseAddress topAddress bytesInWord sourceFuel targetFuel expression value
                  _exceptionRel (hbytesInWord context bytesInWord)
                  (fun name value hvalue =>
                    hlookup context sourceLocals name value hvalue)
                  hrel hsourceValue
              have hsourceEq := Option.some.inj
                (hsourceExpected.symm.trans hsource)
              have hcrepEq := Option.some.inj
                (hcrepExpected.symm.trans hcrep)
              cases hsourceEq
              cases hcrepEq
              simp [panValuePcControlLabelSafe]

theorem panValueCrepProgramStateCorrect_and_controlSafe_return_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (expression : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect (.return expression.toExp) ∧
      PanValueCrepProgramStateControlSafe (.return expression.toExp) := by
  constructor
  · exact panValueCrepProgramStateCorrect_return_source_word expression
      hbytesInWord hlookup
  · exact panValueCrepProgramStateControlSafe_return_source_word expression
      hbytesInWord hlookup

theorem panValueCrepProgramStateControlSafe_seq
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (first second : Prog α)
    (hfirstCorrect : PanValueCrepProgramStateCorrect first)
    (hfirstSafe : PanValueCrepProgramStateControlSafe first)
    (hsecondSafe : PanValueCrepProgramStateControlSafe second) :
    PanValueCrepProgramStateControlSafe (.seq first second) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hcompile :
      compileProg context (.seq first second) =
        .seq (compileProg context first) (compileProg context second) := by
    simp [compileProg]
  rw [hcompile] at hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases hfirstSource : evalPanValueProgWithPrimitiveCallsAndFfi
              primitive sourceHandler structs sourceFunctions
              baseAddress topAddress bytesInWord sourceFuel
              sourceLocals sourceGlobals sourceMemory first with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                hfirstSource] at hsource
          | some firstSourceResult =>
              cases hfirstCrep : evalCrepFullProgState functions crepPrimitive ffi sharedMem
                  baseAddress topAddress targetFuel state (compileProg context first) with
              | none =>
                  simp [evalCrepFullProgState, hfirstCrep] at hcrep
              | some firstCrepResult =>
                  have hfirstSafeResult := hfirstSafe context structs sourceFunctions functions
                    sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                    sourceFuel targetFuel exceptionRel firstSourceResult firstCrepResult
                    hrel hfirstSource hfirstCrep
                  have hfirstRel := hfirstCorrect context structs sourceFunctions functions
                    sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                    sourceFuel targetFuel exceptionRel firstSourceResult firstCrepResult
                    hrel hfirstSource hfirstCrep
                  cases firstSourceResult with
                  | normal firstLocals firstGlobals firstMemory =>
                      cases firstCrepResult with
                      | normal firstState =>
                          have hstateRel :
                              panValueCrepStateRel structs context firstLocals firstGlobals
                                firstMemory firstState := by
                            simpa [panValueCrepControlRel] using hfirstRel
                          have hsourceSecond :
                              evalPanValueProgWithPrimitiveCallsAndFfi
                                primitive sourceHandler structs sourceFunctions
                                baseAddress topAddress bytesInWord sourceFuel
                                firstLocals firstGlobals firstMemory second =
                              some sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepSecond :
                              evalCrepFullProgState functions crepPrimitive ffi sharedMem
                                baseAddress topAddress targetFuel firstState
                                (compileProg context second) = some crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          exact hsecondSafe context structs sourceFunctions functions
                            firstLocals firstGlobals firstMemory firstState primitive
                            sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
                            bytesInWord sourceFuel targetFuel exceptionRel sourceResult
                            crepResult hstateRel hsourceSecond hcrepSecond
                      | returned firstState values
                      | raised firstState exception
                      | broke firstState label
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                  | returned firstLocals firstGlobals firstMemory values =>
                      cases firstCrepResult with
                      | normal firstState
                      | raised firstState exception
                      | broke firstState label
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | returned firstState firstValues =>
                          have hsourceEq :
                              PanValueControlResult.returned firstLocals firstGlobals
                                  firstMemory values = sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepEq :
                              CrepControlResult.returned firstState firstValues = crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstSafeResult
                  | raised firstLocals firstGlobals firstMemory exception value =>
                      cases firstCrepResult with
                      | normal firstState
                      | returned firstState values
                      | broke firstState label
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | raised firstState exceptionCode =>
                          have hsourceEq :
                              PanValueControlResult.raised firstLocals firstGlobals
                                  firstMemory exception value = sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepEq :
                              CrepControlResult.raised firstState exceptionCode = crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstSafeResult
                  | broke firstLocals firstGlobals firstMemory =>
                      cases firstCrepResult with
                      | normal firstState
                      | returned firstState values
                      | raised firstState exception
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | broke firstState label =>
                          have hsourceEq :
                              PanValueControlResult.broke firstLocals firstGlobals
                                  firstMemory = sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepEq :
                              CrepControlResult.broke firstState label = crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstSafeResult
                  | continued firstLocals firstGlobals firstMemory =>
                      cases firstCrepResult with
                      | normal firstState
                      | returned firstState values
                      | raised firstState exception
                      | broke firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | continued firstState label =>
                          have hsourceEq :
                              PanValueControlResult.continued firstLocals firstGlobals
                                  firstMemory = sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepEq :
                              CrepControlResult.continued firstState label = crepResult := by
                            simpa [evalCrepFullProgState, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstSafeResult

theorem panValueCrepProgramStateControlSafe_statefulCompact
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α) (hprogram : StatefulCompactProg α program) :
    PanValueCrepProgramStateControlSafe program := by
  induction hprogram with
  | skip => exact panValueCrepProgramStateControlSafe_skip
  | tick => exact panValueCrepProgramStateControlSafe_tick
  | controlBreak => exact panValueCrepProgramStateControlSafe_break
  | controlContinue => exact panValueCrepProgramStateControlSafe_continue
  | annot tag text => exact panValueCrepProgramStateControlSafe_annot tag text
  | returnConst value =>
      exact panValueCrepProgramStateControlSafe_return_const value
  | raiseWithEvidence exception value hraiseState hraisePlain =>
      exact panValueCrepProgramStateControlSafe_raise exception value
  | @seq first second hfirst hsecond ihfirst ihsecond =>
      exact panValueCrepProgramStateControlSafe_seq first second
        (panValueCrepProgramStateCorrect_statefulCompact first hfirst)
        ihfirst ihsecond

theorem panValueCrepProgramStateCorrect_and_controlSafe_skip
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateCorrect (.skip : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.skip : Prog α) :=
  ⟨panValueCrepProgramStateCorrect_skip,
    panValueCrepProgramStateControlSafe_skip⟩

theorem panValueCrepProgramStateCorrect_and_controlSafe_tick
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateCorrect (.tick : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.tick : Prog α) :=
  ⟨panValueCrepProgramStateCorrect_tick,
    panValueCrepProgramStateControlSafe_tick⟩

theorem panValueCrepProgramStateCorrect_and_controlSafe_annot
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (tag text : String) :
    PanValueCrepProgramStateCorrect (.annot tag text : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.annot tag text : Prog α) :=
  ⟨panValueCrepProgramStateCorrect_annot tag text,
    panValueCrepProgramStateControlSafe_annot tag text⟩

theorem panValueCrepProgramStateCorrect_and_controlSafe_break
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateCorrect (.break : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.break : Prog α) :=
  ⟨panValueCrepProgramStateCorrect_break,
    panValueCrepProgramStateControlSafe_break⟩

theorem panValueCrepProgramStateCorrect_and_controlSafe_continue
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramStateCorrect (.continue : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.continue : Prog α) :=
  ⟨panValueCrepProgramStateCorrect_continue,
    panValueCrepProgramStateControlSafe_continue⟩

theorem panValueCrepProgramStateCorrect_and_controlSafe_seq
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (first second : Prog α)
    (hfirstCorrect : PanValueCrepProgramStateCorrect first)
    (hfirstSafe : PanValueCrepProgramStateControlSafe first)
    (hsecondCorrect : PanValueCrepProgramStateCorrect second)
    (hsecondSafe : PanValueCrepProgramStateControlSafe second) :
    PanValueCrepProgramStateCorrect (.seq first second) ∧
      PanValueCrepProgramStateControlSafe (.seq first second) :=
  ⟨panValueCrepProgramStateCorrect_seq first second hfirstCorrect hsecondCorrect,
    panValueCrepProgramStateControlSafe_seq first second hfirstCorrect hfirstSafe
      hsecondSafe⟩

theorem panValueCrepProgramStateCorrect_and_controlSafe_statefulCompact
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α) (hprogram : StatefulCompactProg α program) :
    PanValueCrepProgramStateCorrect program ∧
      PanValueCrepProgramStateControlSafe program := by
  exact ⟨panValueCrepProgramStateCorrect_statefulCompact program hprogram,
    panValueCrepProgramStateControlSafe_statefulCompact program hprogram⟩

theorem panValueCrepProgramStateControlSafe_ite_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (thenBranch elseBranch : Prog α)
    (hthenSafe : PanValueCrepProgramStateControlSafe thenBranch)
    (helseSafe : PanValueCrepProgramStateControlSafe elseBranch)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateControlSafe
      (.ite condition.toExp thenBranch elseBranch) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          cases hcondition : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord condition.toExp with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcondition] at hsource
          | some conditionValue =>
              cases conditionValue with
              | word sourceCondition =>
                  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
                    compileSourceWordExp_relation context structs sourceLocals
                      sourceGlobals sourceMemory state.locals state.memory
                      baseAddress topAddress bytesInWord
                      (hbytesInWord context bytesInWord)
                      hrel.2.1 (hlookup context sourceLocals) condition
                      sourceCondition hcondition
                  have hcompile : compileProg context
                      (.ite condition.toExp thenBranch elseBranch) =
                      .ite compiledCondition (compileProg context thenBranch)
                        (compileProg context elseBranch) := by
                    simp [compileProg, hcompileCondition]
                  have hcrepConditionState :
                      evalCrepFullExpState state baseAddress topAddress
                        compiledCondition = some sourceCondition := by
                    obtain ⟨compiledCondition', hcompileCondition', hnoGlobal⟩ :=
                      compileSourceWordExp_noGlobal context structs sourceLocals
                        sourceGlobals sourceMemory baseAddress topAddress bytesInWord
                        (hlookup context sourceLocals) condition sourceCondition
                        hcondition
                    have hcompiledEq : compiledCondition = compiledCondition' := by
                      have hpair : ([compiledCondition], Shape.one) =
                          ([compiledCondition'], Shape.one) :=
                        hcompileCondition.symm.trans hcompileCondition'
                      exact (List.cons.inj (congrArg Prod.fst hpair)).1
                    have hcrepCondition' :
                        evalCrepFullExp state.locals state.memory
                          baseAddress topAddress compiledCondition' =
                          some sourceCondition := by
                      simpa [hcompiledEq] using hcrepCondition
                    rw [hcompiledEq]
                    rw [evalCrepFullExpState_eq_of_noGlobal state
                      baseAddress topAddress compiledCondition' hnoGlobal]
                    exact hcrepCondition'
                  rw [hcompile] at hcrep
                  by_cases hnonzero : sourceCondition ≠ 0
                  · have hsourceThen :
                        evalPanValueProgWithPrimitiveCallsAndFfi
                          primitive sourceHandler structs sourceFunctions
                          baseAddress topAddress bytesInWord sourceFuel
                          sourceLocals sourceGlobals sourceMemory thenBranch =
                          some sourceResult := by
                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                        evalPanValueExp, hcondition, hnonzero] using hsource
                    have hcrepThen :
                        evalCrepFullProgState functions crepPrimitive ffi sharedMem
                          baseAddress topAddress targetFuel state
                          (compileProg context thenBranch) = some crepResult := by
                      simpa [evalCrepFullProgState, hcrepConditionState, hnonzero] using hcrep
                    exact hthenSafe context structs sourceFunctions functions
                      sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                      crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                      sourceFuel targetFuel exceptionRel sourceResult crepResult hrel
                      hsourceThen hcrepThen
                  · have hzero : sourceCondition = 0 := by
                      exact Classical.byContradiction (fun hnot => hnonzero hnot)
                    have hsourceElse :
                        evalPanValueProgWithPrimitiveCallsAndFfi
                          primitive sourceHandler structs sourceFunctions
                          baseAddress topAddress bytesInWord sourceFuel
                          sourceLocals sourceGlobals sourceMemory elseBranch =
                          some sourceResult := by
                      simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                        evalPanValueExp, hcondition, hnonzero] using hsource
                    have hcrepElse :
                        evalCrepFullProgState functions crepPrimitive ffi sharedMem
                          baseAddress topAddress targetFuel state
                          (compileProg context elseBranch) = some crepResult := by
                      simpa [evalCrepFullProgState, hcrepConditionState, hnonzero] using hcrep
                    exact helseSafe context structs sourceFunctions functions
                      sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                      crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                      sourceFuel targetFuel exceptionRel sourceResult crepResult hrel
                      hsourceElse hcrepElse
              | rStruct fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcondition] at hsource
              | nStruct name fields =>
                  simp [evalPanValueProgWithPrimitiveCallsAndFfi, hcondition] at hsource

/-! A conditional source program needs both halves of the `pc_compile_correct`
    obligation: the stateful evaluator simulation and the final label-zero
    control safety rule.  Keep them paired so a future conditional proof
    cannot discharge only the control observation while omitting execution
    correctness. -/
theorem panValueCrepProgramStateCorrect_and_controlSafe_ite_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (thenBranch elseBranch : Prog α)
    (hthenCorrect : PanValueCrepProgramStateCorrect thenBranch)
    (helseCorrect : PanValueCrepProgramStateCorrect elseBranch)
    (hthenSafe : PanValueCrepProgramStateControlSafe thenBranch)
    (helseSafe : PanValueCrepProgramStateControlSafe elseBranch)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.ite condition.toExp thenBranch elseBranch) ∧
      PanValueCrepProgramStateControlSafe
        (.ite condition.toExp thenBranch elseBranch) := by
  constructor
  · exact panValueCrepProgramStateCorrect_ite_source_word condition
      thenBranch elseBranch hthenCorrect helseCorrect hbytesInWord hlookup
  · exact panValueCrepProgramStateControlSafe_ite_source_word condition
      thenBranch elseBranch hthenSafe helseSafe hbytesInWord hlookup

theorem panValueCrepProgramStateControlSafe_while_of_loop_safe
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (body : Prog α)
    (hloopSafe : PanValueCrepProgramLoopStateControlSafe
      (.while condition.toExp body)) :
    PanValueCrepProgramStateControlSafe
      (.while condition.toExp body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel _exceptionRel
    sourceResult crepResult hrel hsource hcrep
  exact hloopSafe context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel sourceResult crepResult
    hrel hsource hcrep

/-! Pair the stateful while simulation with its final Pc control-safety
    obligation.  The body needs the loop-aware safety relation used by the
    evaluator induction, while the complete while program separately needs
    the boundary label-zero relation. -/
theorem panValueCrepProgramStateCorrect_and_controlSafe_while_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : SourceWordExp α) (body : Prog α)
    (hbody : PanValueCrepProgramStateCorrect body)
    (hbodySafe : PanValueCrepProgramLoopStateControlSafe body)
    (hloopSafe : PanValueCrepProgramLoopStateControlSafe
      (.while condition.toExp body))
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.while condition.toExp body) ∧
      PanValueCrepProgramStateControlSafe
        (.while condition.toExp body) := by
  constructor
  · exact panValueCrepProgramStateCorrect_while_source_word condition body
      hbody hbodySafe hbytesInWord hlookup
  · exact panValueCrepProgramStateControlSafe_while_of_loop_safe condition
      body hloopSafe

theorem panValueCrepProgramLoopStateControlSafe_while_zero
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (body : Prog α) :
    PanValueCrepProgramLoopStateControlSafe
      (.while (SourceWordExp.const (0 : α)).toExp body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProgState] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi,
            SourceWordExp.toExp, evalPanValueExp,
            evalCrepFullProgState, evalCrepFullExpState, compileProg,
            compileExp] at hsource hcrep
          cases hsource
          cases hcrep
          simp

structure PanValuePcInput (α : Type u) where
  structs : StructContext
  code : PanValuePcSourceCode α
  eshapes : InfoMap Shape
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  memory : α → Option (PanValue α)

structure CrepPcInput (α : Type u) where
  structs : StructContext
  code : PanValuePcTargetCode α
  eshapes : InfoMap Shape
  state : CrepState α

structure PanValuePcExecution (α : Type u) where
  code : PanValuePcSourceCode α
  eshapes : InfoMap Shape
  result : PanValuePcResult α

structure CrepPcExecution (α : Type u) where
  code : PanValuePcTargetCode α
  eshapes : InfoMap Shape
  result : CrepPcResult α

abbrev PanValuePcEvaluator (α : Type u) :=
  CompileContext α → PanValuePcInput α → Prog α → Option (PanValuePcExecution α)

abbrev CrepPcEvaluator (α : Type u) :=
  CompileContext α → CrepPcInput α → CrepProg α → Option (CrepPcExecution α)

/-! The direct Lean analogue of the quantifier/implication shape of HOL
`pc_compile_correct`: code/exceptions/localisation assumptions, related
initial source/target state, successful non-error source and compiled-target
evaluations, then the complete result relation. -/
def PanValuePcCompileCorrect
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceExecution : PanValuePcExecution α)
    (targetExecution : CrepPcExecution α),
    sourceInput.structs = structs →
    targetInput.structs = structs →
    panValuePcLocalisedCode sourceInput.code →
    localisedProg program →
    codeRel context sourceInput.code targetInput.code →
    excpRel context sourceInput.eshapes targetInput.eshapes →
    panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
      sourceInput.memory targetInput.state →
    sourceExecution.result ≠ .error →
    sourceEvaluate context sourceInput program = some sourceExecution →
    targetEvaluate context targetInput (compileProg context program) =
      some targetExecution →
    codeRel context sourceExecution.code targetExecution.code →
    excpRel context sourceExecution.eshapes targetExecution.eshapes →
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        sourceExecution.result targetExecution.result

def PanValuePcCompileCorrectWithContextCode
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceExecution : PanValuePcExecution α)
    (targetExecution : CrepPcExecution α),
    sourceInput.structs = structs →
    targetInput.structs = structs →
    panValuePcLocalisedCode sourceInput.code →
    localisedProg program →
    codeRel context sourceInput.code targetInput.code →
    excpRel context sourceInput.eshapes targetInput.eshapes →
    panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
      sourceInput.memory targetInput.state →
    sourceExecution.result ≠ .error →
    sourceEvaluate context sourceInput program = some sourceExecution →
    targetEvaluate context targetInput (compileProg context program) =
      some targetExecution →
    codeRel context sourceExecution.code targetExecution.code →
    excpRel context sourceExecution.eshapes targetExecution.eshapes →
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup sourceExecution.result targetExecution.result

/-! The context-coded result relation strengthens only the raised clause with
the exact Cake exception-code provenance.  Consequently the plain result
relation is a projection of it, and a context-coded compiler-correctness
instance yields the plain boundary instance.  These projections let plain
consumers reuse the context-coded constructor bridges without restating the
exception-code premise. -/
theorem panValuePcExceptionResultRel_of_withContextCode
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException : α)
    (h : panValuePcExceptionResultRelWithContextCode structs context
      exceptionRel exceptionCode globalsLookup sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException) :
    panValuePcExceptionResultRel structs context exceptionRel exceptionCode
      globalsLookup sourceGlobals sourceMemory sourceException sourceValue
      targetState targetException :=
  h.1

theorem panValuePcResultRel_of_withContextCode
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceResult : PanValuePcResult α) (targetResult : CrepPcResult α)
    (h : panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup sourceResult targetResult) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      sourceResult targetResult := by
  cases sourceResult <;> cases targetResult <;>
    simp only [panValuePcResultRelWithContextCode, panValuePcResultRel] at h ⊢ <;>
    (try exact h) <;> (try exact ⟨h.1, h.2.1⟩)

theorem panValuePcCompileCorrect_of_withContextCode
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α)
    (h : PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
    hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  exact panValuePcResultRel_of_withContextCode structs context exceptionRel
    exceptionCode globalsLookup sourceExecution.result targetExecution.result
    (h context structs sourceInput targetInput exceptionRel sourceExecution
      targetExecution hsourceStructs htargetStructs hlocalisedCode hlocalised
      hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp)

/-! Packaging theorem for a supported compiler subset.  Every HOL result case
is an explicit obligation; in particular no proof can discharge this
boundary by silently dropping timeout or FinalFFI. -/
theorem panValuePcCompileCorrect_of_obligations
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α)
    (hobligation : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceExecution : PanValuePcExecution α)
      (targetExecution : CrepPcExecution α),
      sourceInput.structs = structs →
      targetInput.structs = structs →
      panValuePcLocalisedCode sourceInput.code →
      localisedProg program →
      codeRel context sourceInput.code targetInput.code →
      excpRel context sourceInput.eshapes targetInput.eshapes →
      panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
        sourceInput.memory targetInput.state →
      sourceExecution.result ≠ .error →
      sourceEvaluate context sourceInput program = some sourceExecution →
      targetEvaluate context targetInput (compileProg context program) =
        some targetExecution →
      codeRel context sourceExecution.code targetExecution.code →
      excpRel context sourceExecution.eshapes targetExecution.eshapes →
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        sourceExecution.result targetExecution.result) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hlocalisedCode hlocalised hcode hexcp hstate
    hnonerror hsource htarget hpostCode hpostExcp
  exact hobligation context structs sourceInput targetInput exceptionRel
    sourceExecution targetExecution hlocalisedCode hlocalised hcode
    hexcp hstate hnonerror hsource htarget hpostCode hpostExcp

/-! Context-coded counterpart of `panValuePcCompileCorrect_of_obligations`.
    The context-specific exception/global relation remains explicit at every
    evaluator boundary; no result case is collapsed into the ordinary relation.
-/
theorem panValuePcCompileCorrectWithContextCode_of_obligations
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α)
    (hobligation : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceExecution : PanValuePcExecution α)
      (targetExecution : CrepPcExecution α),
      sourceInput.structs = structs →
      targetInput.structs = structs →
      panValuePcLocalisedCode sourceInput.code →
      localisedProg program →
      codeRel context sourceInput.code targetInput.code →
      excpRel context sourceInput.eshapes targetInput.eshapes →
      panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
        sourceInput.memory targetInput.state →
      sourceExecution.result ≠ .error →
      sourceEvaluate context sourceInput program = some sourceExecution →
      targetEvaluate context targetInput (compileProg context program) =
        some targetExecution →
      codeRel context sourceExecution.code targetExecution.code →
      excpRel context sourceExecution.eshapes targetExecution.eshapes →
      panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
        globalsLookup sourceExecution.result targetExecution.result) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate codeRel
      excpRel exceptionCode globalsLookup program := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hlocalisedCode hlocalised hcode hexcp hstate
    hnonerror hsource htarget hpostCode hpostExcp
  exact hobligation context structs sourceInput targetInput exceptionRel
    sourceExecution targetExecution hlocalisedCode hlocalised hcode
    hexcp hstate hnonerror hsource htarget hpostCode hpostExcp

/-! Assemble explicit context-coded evaluator obligations into the ordinary
    `pc_compile_correct` boundary.  The source/target state, code, exception,
    and every evaluator result premise remain visible to the caller. -/
theorem panValuePcCompileCorrect_of_context_code_obligations
    [BEq α] [OfNat α 0] [Add α]
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (program : Prog α)
    (hobligation : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceExecution : PanValuePcExecution α)
      (targetExecution : CrepPcExecution α),
      sourceInput.structs = structs →
      targetInput.structs = structs →
      panValuePcLocalisedCode sourceInput.code →
      localisedProg program →
      codeRel context sourceInput.code targetInput.code →
      excpRel context sourceInput.eshapes targetInput.eshapes →
      panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
        sourceInput.memory targetInput.state →
      sourceExecution.result ≠ .error →
      sourceEvaluate context sourceInput program = some sourceExecution →
      targetEvaluate context targetInput (compileProg context program) =
        some targetExecution →
      codeRel context sourceExecution.code targetExecution.code →
      excpRel context sourceExecution.eshapes targetExecution.eshapes →
      panValuePcResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceExecution.result targetExecution.result) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program := by
  apply panValuePcCompileCorrect_of_withContextCode sourceEvaluate targetEvaluate
    codeRel excpRel exceptionCode globalsLookup program
  exact panValuePcCompileCorrectWithContextCode_of_obligations
    sourceEvaluate targetEvaluate codeRel excpRel exceptionCode globalsLookup
    program hobligation

end Flapjack
