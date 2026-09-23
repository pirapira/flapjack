import Flapjack.FiniteMap
import Flapjack.HolRef
import Flapjack.PanBst
import Flapjack.PanLocalised
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

/-! Finite-map lookups needed by the extracted compiler are represented in its
list-backed executable context.  Repeated keys are harmless: every projected
entry carries the same finite-map lookup result, and first-match lookup thus
agrees with `FLOOKUP` for every requested key. -/
def projectFiniteMapToInfoMap [BEq String] (keys : List String)
    (entries : FiniteMap String β) : InfoMap β :=
  keys.filterMap fun key =>
    (FLOOKUP entries key).map fun value => (key, value)

def functionsUsedByProg : Prog α → List FunName
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .store32 _ _ |
      .storeByte _ _ | .break | .continue | .extCall _ _ _ _ _ | .raise _ _ |
      .return _ | .shMemLoad _ _ _ _ | .shMemStore _ _ _ | .tick | .annot _ _ => []
  | .dec _ _ _ body => functionsUsedByProg body
  | .seq first second => functionsUsedByProg first ++ functionsUsedByProg second
  | .ite _ thenBranch elseBranch =>
      functionsUsedByProg thenBranch ++ functionsUsedByProg elseBranch
  | .while _ body => functionsUsedByProg body
  | .call info function _ =>
      function :: (match info with
        | some (_, some (_, _, handler)) => functionsUsedByProg handler
        | _ => [])
  | .decCall _ _ function _ body => function :: functionsUsedByProg body
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! Flapjack-specific projection support, not a port of HOL `free_var_ids`.
    HOL's `free_var_ids` intentionally omits Global call destinations, but
    `pan_to_crep$compile` looks up a call destination in `ctxt.vars` regardless
    of its kind. Keep `freeVarIds` faithful and additionally retain every name
    the executable call compiler queries, including handler payload names. -/
def callVarsUsedByProg : Prog α → List VarName
  | .dec _ _ _ body => callVarsUsedByProg body
  | .seq first second => callVarsUsedByProg first ++ callVarsUsedByProg second
  | .ite _ thenBranch elseBranch =>
      callVarsUsedByProg thenBranch ++ callVarsUsedByProg elseBranch
  | .while _ body => callVarsUsedByProg body
  | .call info _ _ =>
      match info with
      | none => []
      | some (destination, handler) =>
          (match destination with
           | none => []
           | some (_, name) => [name]) ++
          (match handler with
           | none => []
           | some (_, name, body) => name :: callVarsUsedByProg body)
  | .decCall _ _ _ _ body => callVarsUsedByProg body
  | _ => []
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def compileCodeRelContext [BEq String] (context : PanToCrepProofContext α)
    (program : Prog α) : PanToCrepCompileContext α :=
  { vars := projectFiniteMapToInfoMap
      (freeVarIds program ++ callVarsUsedByProg program) context.vars
    functions := projectFiniteMapToInfoMap (functionsUsedByProg program) context.funcs
    exceptions := projectFiniteMapToInfoMap (expIds program) context.eids
    maxVar := context.vmax }

/-! Execute the Pan-to-Crep compiler with the HOL proof context. The map
projection is limited to names syntactically queried by `compileProg`, and the
word stride comes from the fixed `CrepBytesInWord` instance, not a context
field. -/
def compileCodeRelProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    [BEq String] (context : PanToCrepProofContext α) (program : Prog α) :
    CrepProg α :=
  compileProgFixed (compileCodeRelContext context program) program

/-! HOL-shaped `code_rel_def` relation (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:32`).
    It quantifies over every source code entry, requires localisation and the
    exact parameter/return-shape lookup in `ctxt.funcs`, derives parameter
    slots from `GENLIST I (size_of_shape (Comb shs))`, constructs the target
    context with `ctxt_fc`, and relates that entry to its compiled body.

    This is intentionally untagged: its body currently uses the list-backed
    `compileProg` adapter. The source HOL definition concludes with exact HOL
    `compile`, whose fixed byte-width behavior is tracked separately by bead
    `flapjack-pxn.18.3.1.4`. -/
def codeRel [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    [BEq String]
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
