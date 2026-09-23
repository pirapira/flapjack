import Flapjack.FiniteMap
import Flapjack.HolRef
import Flapjack.PanBst
import Flapjack.PanLocalised
import Flapjack.PanValueFlatten
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.PanToCrepMaxList

/-!
Faithful HOL-facing relations and contexts for the Pancake `pan_to_crep`
correctness proof.  The definitions here use the extensional finite-map model
from `Flapjack.FiniteMap`, rather than the list-backed executable compiler
context.
-/

namespace Flapjack

/-! The HOL proof context record used by `ctxt_fc_def`. -/
structure PanToCrepProofContext (α : Type) where
  vars : FiniteMap String (Shape × List Nat)
  funcs : FiniteMap String (List (String × Shape) × Shape)
  eids : FiniteMap String α
  vmax : Nat

/-! HOL `excp_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:16`).
    This states equality of exception-code map domains and injectivity of the
    compiler's code map on its defined entries; the source exception map's
    values need not equal the compiler's values. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "excp_rel_def"]
def excpRel
    (compilerCodes : FiniteMap String α)
    (sourceShapes : FiniteMap String β) : Prop :=
  FDOM sourceShapes = FDOM compilerCodes ∧
    ∀ exception exception' code code',
      FLOOKUP compilerCodes exception = some code →
      FLOOKUP compilerCodes exception' = some code' →
      code = code' → exception = exception'

/-! HOL `ctxt_fc_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:25`).
    `FUPDATE_LIST` and `withShape` preserve the source definition's ZIP
    truncation and TAKE/DROP slicing, and `maxList` is Cake's `MAX_LIST`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_def"]
def ctxtFc
    (compilerFunctions : FiniteMap String (List (String × Shape) × Shape))
    (exceptionCodes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) : PanToCrepProofContext α :=
  { vars := FUPDATE_LIST FEMPTY
      (variables.zip (shapes.zip (withShape shapes names)))
    funcs := compilerFunctions
    eids := exceptionCodes
    vmax := maxList names }

/-- HOL `ctxt_fc_funcs_eq`: constructing a function context preserves the
    supplied function map. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_funcs_eq"]
theorem ctxtFcFuncsEq
    (functions : FiniteMap String (List (String × Shape) × Shape))
    (codes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) :
    (ctxtFc functions codes variables shapes names).funcs = functions := rfl

/-- HOL `ctxt_fc_eids_eq`: constructing a function context preserves the
    supplied exception-code map. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_eids_eq"]
theorem ctxtFcEidsEq
    (functions : FiniteMap String (List (String × Shape) × Shape))
    (codes : FiniteMap String α) (variables : List String)
    (shapes : List Shape) (names : List Nat) :
    (ctxtFc functions codes variables shapes names).eids = codes := rfl

/-- HOL `ctxt_fc_vmax`: the constructed context's maximum slot is the
    maximum of the supplied slot list. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_vmax"]
theorem ctxtFcVmax
    (context : PanToCrepProofContext α) (codes : FiniteMap String α)
    (variables : List String) (shapes : List Shape) (names : List Nat) :
    (ctxtFc context.funcs codes variables shapes names).vmax = maxList names := rfl

/-- HOL `ctxt_max_el_leq`: a slot selected from a variable's flattened name
    list does not exceed the context's maximum slot. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_max_el_leq"]
theorem ctxtMaxGetElemLe
    (context : PanToCrepProofContext α) (varName : String)
    (shape : Shape) (names : List Nat) (index : Nat)
    (hmax : ctxtMax context.vmax context.vars)
    (hlookup : FLOOKUP context.vars varName = some (shape, names))
    (hindex : index < names.length) :
    names[index] ≤ context.vmax := by
  exact hmax.2 varName shape names hlookup names[index] (List.getElem_mem hindex)

/-- HOL `slc_def`: pair each source parameter name with its argument value,
    with `ZIP` truncation represented by Lean's `List.zip`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "slc_def"]
def slc [BEq String] (parameters : List (String × Shape))
    (arguments : List (PanValue α)) : FiniteMap String (PanValue α) :=
  FUPDATE_LIST FEMPTY ((parameters.map Prod.fst).zip arguments)

/-- HOL `tlc_def`: pair target slots with the flattened argument words. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "tlc_def"]
def tlc [BEq Nat] (slots : List Nat) (arguments : List (PanValue α)) :
    FiniteMap Nat α :=
  FUPDATE_LIST FEMPTY (slots.zip (arguments.flatMap panValueFlatten))

/-- HOL `slc_tlc_rw`: both local-map constructor names unfold to their
    original finite-map updates. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "slc_tlc_rw"]
theorem slcTlcRw [BEq String] [BEq Nat]
    (parameters : List (String × Shape)) (slots : List Nat)
    (arguments : List (PanValue α)) :
    (FUPDATE_LIST FEMPTY ((parameters.map Prod.fst).zip arguments) =
      slc parameters arguments) ∧
    (FUPDATE_LIST FEMPTY (slots.zip (arguments.flatMap panValueFlatten)) =
      tlc slots arguments) := ⟨rfl, rfl⟩

/-! HOL `state_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:47`).
    The source Pancake state and target Crepe state agree on their memory
    domains, clock, endianness, FFI state, and address bounds; the source has
    no struct context (`s.structs = []`) and no globals (`s.globals = FEMPTY`).
    `word_lab` is a single-constructor type, so the target's raw word cells
    reconstruct the source `PanValue` cells with `PanValue.word`; a source cell
    that stored a structure could not be recovered from the target memory and
    therefore does not satisfy the relation. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_def"]
def stateRel (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ) : Prop :=
  s.memory = (fun address => (t.memory address).map PanValue.word) ∧
    s.memaddrs = t.memaddrs ∧
    s.sharedMemaddrs = t.shMemaddrs ∧ s.structs = [] ∧
    s.globals = (FEMPTY : FiniteMap VarName (PanValue α)) ∧
    s.clock = t.clock ∧ s.be = t.bigEndian ∧ s.ffi = t.ffi ∧
    s.baseAddress = t.baseAddress ∧ s.topAddress = t.topAddress

/-- HOL `state_rel_structs[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:54`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_structs"]
theorem stateRel_structs (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ)
    (hrel : stateRel s t) : s.structs = [] := by
  rcases hrel with ⟨_, _, _, hstructs, _, _, _, _, _, _⟩
  exact hstructs

/-- HOL `state_rel_globals[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:55`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_globals"]
theorem stateRel_globals (s : PanSemState α (FfiState σ)) (t : CrepRuntimeState α σ)
    (hrel : stateRel s t) : s.globals = (FEMPTY : FiniteMap VarName (PanValue α)) := by
  rcases hrel with ⟨_, _, _, _, hglobals, _, _, _, _, _⟩
  exact hglobals

/-- HOL `locals_rel_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:71`):
    the proof context's variable map is well formed, and every live source
    variable is recovered in the target locals by mapping its slot list through
    the target map, with the flattened value equal to the produced word list and
    the variable's shape well formed against the empty struct context. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_def"]
def localsRel (context : PanToCrepProofContext α)
    (sLocals : FiniteMap String (PanValue α))
    (tLocals : FiniteMap Nat α) : Prop :=
  noOverlap context.vars ∧ ctxtMax context.vmax context.vars ∧
    ∀ vname v, FLOOKUP sLocals vname = some v →
      ∃ ns vs, FLOOKUP context.vars vname = some (panValueShape [] v, ns) ∧
        ns.mapM (FLOOKUP tLocals) = some vs ∧ panValueFlatten v = vs ∧
        isWfShape [] (panValueShape [] v) = true

/-- HOL `locals_rel_wf_shape`: every source local covered by the local-state
    relation is a well-formed value in the empty struct context. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_wf_shape"]
theorem localsRelWfShape
    (context : PanToCrepProofContext α)
    (sourceLocals : FiniteMap String (PanValue α))
    (targetLocals : FiniteMap Nat α) (name : String) (value : PanValue α)
    (hrel : localsRel context sourceLocals targetLocals)
    (hlookup : FLOOKUP sourceLocals name = some value) :
    panValueIsWf [] value = true := by
  obtain ⟨_, _, hmembers⟩ := hrel
  obtain ⟨_, _, _, _, _, hshape⟩ := hmembers name value hlookup
  rw [← panValueIsWf_eq_isWfShape_panValueShape_of_nil [] value rfl]
  exact hshape

/-- HOL `local_rel_gt_vmax_preserved`: a target local slot strictly above the
    proof context's maximum cannot occur in any source variable's slot list. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "local_rel_gt_vmax_preserved"]
theorem localRelGtVmaxPreserved
    (context : PanToCrepProofContext α)
    (sourceLocals : FiniteMap String (PanValue α))
    (targetLocals : FiniteMap Nat α) (slot : Nat) (newValue : α)
    (hrel : localsRel context sourceLocals targetLocals)
    (habove : context.vmax < slot) :
    localsRel context sourceLocals (FUPDATE targetLocals (slot, newValue)) := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  intro name value hlookup
  obtain ⟨names, values, hcontext, hvalues, hflatten, hwf⟩ :=
    hrel.2.2 name value hlookup
  refine ⟨names, values, hcontext, ?_, hflatten, hwf⟩
  rw [← hvalues]
  apply list_mapM_congr
  intro key hkey
  rw [FLOOKUP_update]
  have hle : key ≤ context.vmax :=
    hrel.2.1.2 name (panValueShape [] value) names hcontext key hkey
  have hne : slot ≠ key := by
    intro he
    subst key
    exact (Nat.not_lt_of_ge hle) habove
  simp [beq_eq_false_iff_ne.mpr hne]

/-! Execute the finite-map compiler with the HOL proof context. Every map is
    passed directly to `compileProgHOL`; no queried-name projection to an
    `InfoMap` is performed. -/
def compileCodeRelProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α] (context : PanToCrepProofContext α) (program : Prog α) :
    CrepProg α :=
  compileProgHOL
    { vars := context.vars, funcs := context.funcs, eids := context.eids,
      vmax := context.vmax }
    program

/-! HOL-shaped `code_rel_def` relation (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:32`).
    It quantifies over every source code entry, requires localisation and the
    exact parameter/return-shape lookup in `ctxt.funcs`, derives parameter
    slots from `GENLIST I (size_of_shape (Comb shs))`, constructs the target
    context with `ctxt_fc`, and relates that entry to its compiled body.

    Its compiler conclusion routes to `compileProgHOL`, whose context is the
    original finite-map record and whose definition is tagged to HOL
    `compile_def`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_def"]
def codeRel [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α)) : Prop :=
  ∀ function variableShapes program returnShape,
    FLOOKUP sourceCode function = some (variableShapes, program, returnShape) →
      localisedProg program ∧
      FLOOKUP context.funcs function = some (variableShapes, returnShape) ∧
      let variables := variableShapes.map Prod.fst
      let shapes := variableShapes.map Prod.snd
      let names := List.range (Shape.shapeSize (.comb shapes))
      let nextContext := ctxtFc context.funcs context.eids variables shapes names
      FLOOKUP targetCode function = some
        (names, compileCodeRelProg nextContext program)

end Flapjack
