import Flapjack.FiniteMap
import Flapjack.HolRef
import Flapjack.PanBst
import Flapjack.PanLocalised
import Flapjack.PanValueFlatten
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanSemStateEval
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

/-! Exact utility theorem ports used by the `pan_to_crep` proof development. -/

/-- HOL `MAX_LIST_APPEND`: the maximum of an appended list is the maximum
    of the two constituent maxima. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAX_LIST_APPEND"]
theorem maxListAppendHol (first second : List Nat) :
    maxList (first ++ second) = max (maxList first) (maxList second) :=
  maxList_append first second

/-- HOL `MAX_LIST_NOT_MEM`: a natural number above the list maximum is not
    present in that list. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAX_LIST_NOT_MEM"]
theorem maxListNotMemHol (x : Nat) (values : List Nat)
    (h : x > maxList values) : x ∉ values :=
  maxList_not_mem x values h

/-- HOL `flookup_res_var_thm_quant`: restoring one natural-number local
    changes only that local's lookup. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "flookup_res_var_thm_quant"]
theorem flookupResVarQuant (locals : FiniteMap Nat α)
    (name query : Nat) (value : Option α) :
    FLOOKUP (resVar locals (name, value)) query =
      if query = name then value else FLOOKUP locals query := by
  simpa [beq_iff_eq] using FLOOKUP_resVar locals name query value

/-- HOL `mem_comp_field_lem`: selecting a compiled record field retains an
    input expression or produces the zero fallback. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mem_comp_field_lem"]
theorem compileField_mem_or_zero
    [OfNat α 0]
    (index : Nat) (shapes : List Shape) (expressions : List (CrepExp α))
    (expression : CrepExp α)
    (hmem : expression ∈ (compileField index shapes expressions).1) :
    expression ∈ expressions ∨ expression = .const 0 := by
  induction shapes generalizing index expressions with
  | nil =>
      simp [compileField] at hmem
      exact Or.inr hmem
  | cons shape shapes ih =>
      cases index with
      | zero =>
          left
          exact List.mem_of_mem_take hmem
      | succ index =>
          have hdrop : expression ∈
              (compileField index shapes
                (expressions.drop (Shape.shapeSize shape))).1 := by
            simpa [compileField] using hmem
          rcases ih index (expressions.drop (Shape.shapeSize shape)) hdrop with
            hinput | hzero
          · exact Or.inl (List.mem_of_mem_drop hinput)
          · exact Or.inr hzero

/-- HOL `filter_not_mem_self`: filtering a list by non-membership in that
    same list removes every element. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "filter_not_mem_self"]
theorem filter_not_mem_self {α : Type} [DecidableEq α] (l : List α) :
    l.filter (fun x => decide (x ∉ l)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp [hx]

/-! Cake `not_none_then_some` (`pan_to_crepProofScript.sml:3593`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "not_none_then_some"]
theorem option_ne_none_iff_exists {α : Type} (x : Option α) :
    x ≠ none ↔ ∃ a, x = some a := by
  constructor
  · intro h
    cases x with
    | none => exact absurd rfl h
    | some a => exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact Option.some_ne_none a

/-! Cake `mod_eq_lt_eq` (`pan_to_crepProofScript.sml:4621`): below the
modulus, reduction is the identity. The HOL conjunction of three premises is
represented by Lean's curried theorem arguments. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mod_eq_lt_eq"]
theorem mod_eq_of_lt_eq {n x m : Nat} (hn : n < x) (hm : m < x)
    (h : n % x = m % x) : n = m := by
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at h
  exact h

/-! Cake `pair_map_I` (`pan_to_crepProofScript.sml:4630`): the uncurried pair
constructor is the identity on pairs. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pair_map_I"]
theorem prod_mk_pair_eq_id {α β : Type} :
    (fun p : α × β => (p.1, p.2)) = id := by
  funext p
  cases p
  rfl

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

/-- The state-based 64-bit specialization of Cake
    `opt_mmap_eval_is_wf_shape_v`; its evaluator premise is derived solely
    from `PanSemState`, including its
    word-memory domain, shared-memory domain, and endianness. This remains
    untagged because the HOL theorem is polymorphic over word widths while
    this evaluator uses the RISC-V `BitVec 64` model. -/
theorem evalPanSemStateExpsWfShapeOfStateRel
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0]
    [OfNat (RiscV.Word 64) 1] [OfNat (RiscV.Word 64) 2]
    [OfNat (RiscV.Word 64) 3] [Add (RiscV.Word 64)]
    [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (context : PanToCrepProofContext (RiscV.Word 64))
    (targetLocals : FiniteMap Nat (RiscV.Word 64))
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (heval : evalPanSemStateExps source expressions = some values)
    (hstate : stateRel source target)
    (hlocals : localsRel context source.locals targetLocals) :
    panValueIsWfValues ([] : StructContext) values = true := by
  obtain ⟨_, _, _, hstructs, hglobalsEq, _, _, _, _, _⟩ := hstate
  have hlocalsWf : ∀ name value, source.locals name = some value →
      panValueIsWf ([] : StructContext) value = true := by
    intro name value hlookup
    exact localsRelWfShape context source.locals targetLocals name value
      hlocals hlookup
  have hglobalsWf : ∀ name value, source.globals name = some value →
      panValueIsWf ([] : StructContext) value = true := by
    intro name value hlookup
    rw [hglobalsEq, FEMPTY] at hlookup
    simp at hlookup
  have heval' : evalPanValueExps ([] : StructContext) source.locals
      source.globals source.memory source.baseAddress source.topAddress
      panSemBitVec64BytesInWord expressions
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some values := by
    simpa [evalPanSemStateExps, evalPanSemStateExp, evalPanValueExps,
      panSemBitVec64BytesInWord, hstructs] using heval
  exact evalPanValueExps_isWfShape ([] : StructContext) source.locals
    source.globals source.memory source.baseAddress source.topAddress
    panSemBitVec64BytesInWord hlocalsWf hglobalsWf expressions
    (some (panSemBitVec64MemoryAccess source)) values heval'

/-- Faithful port of Cake `locals_rel_lookup_ctxt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:527`). The HOL
    `OPT_MMAP (FLOOKUP t_locals) ns = SOME (flatten v)` is Lean's `List.mapM`
    result, and `is_wf_shape_nil` is `isWfShape []` at the translated value
    shape. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_lookup_ctxt"]
theorem localsRelLookupCtxt
    (context : PanToCrepProofContext α)
    (sourceLocals : FiniteMap String (PanValue α))
    (targetLocals : FiniteMap Nat α) (name : String) (value : PanValue α)
    (hrel : localsRel context sourceLocals targetLocals)
    (hlookup : FLOOKUP sourceLocals name = some value) :
    ∃ slots,
      FLOOKUP context.vars name = some (panValueShape [] value, slots) ∧
      slots.length = (panValueFlatten value).length ∧
      slots.mapM (FLOOKUP targetLocals) = some (panValueFlatten value) ∧
      isWfShape [] (panValueShape [] value) = true := by
  obtain ⟨slots, values, hcontext, hmap, hflatten, hwf⟩ :=
    hrel.2.2 name value hlookup
  refine ⟨slots, hcontext, ?_, ?_, hwf⟩
  · rw [hflatten]
    exact list_mapM_length (FLOOKUP targetLocals) slots values hmap
  · rw [hflatten]
    exact hmap

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

/-- HOL `code_rel_imp`: an entry in related source code is localised and
    has the corresponding function metadata and compiled target entry. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_imp"]
theorem codeRelImp [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (hrel : codeRel context sourceCode targetCode)
    (function : FunName) (variableShapes : List (VarName × Shape))
    (program : Prog α) (returnShape : Shape)
    (hlookup : FLOOKUP sourceCode function =
      some (variableShapes, program, returnShape)) :
    localisedProg program ∧
      FLOOKUP context.funcs function = some (variableShapes, returnShape) ∧
      let variables := variableShapes.map Prod.fst
      let shapes := variableShapes.map Prod.snd
      let names := List.range (Shape.shapeSize (.comb shapes))
      let nextContext := ctxtFc context.funcs context.eids variables shapes names
      FLOOKUP targetCode function = some
        (names, compileCodeRelProg nextContext program) :=
  hrel function variableShapes program returnShape hlookup

end Flapjack
