import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.CrepToLoop.Optimise
import Flapjack.Pancake.LoopToWord
import Flapjack.Word
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.WordExpressionFlatten
import Flapjack.RiscV.WordSimp
import Flapjack.RiscV.RegAlloc
import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.WordDeadCode
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordInstSelect
import Flapjack.RiscV.WordUnreach
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Loops
import Flapjack.RiscV.Link
import Flapjack.RiscV.Lab
import Flapjack.Display

/-!
An executable composition of the currently ported Pancake passes.

The result keeps each intermediate representation visible so the eventual
simulation theorem can be proved pass by pass. This composition covers the
front-end normalization and structure/global passes, Pancake-to-Crepe,
Crepe-to-Loop, and Loop-to-Word. The typed RISC-V artifact boundary is also
exposed, while instruction selection remains partial in
`Flapjack.RiscV.Backend`.
-/

namespace Flapjack

def pipelineExceptionCodes (fromNat : Nat → α) : Nat → List (Decl α) → InfoMap α
  | _, [] => []
  | index, .exnDecl exception _ :: declarations =>
      (exception, fromNat index) :: pipelineExceptionCodes fromNat (index + 1) declarations
  | index, _ :: declarations => pipelineExceptionCodes fromNat index declarations

/-! Source-shaped port of Pancake's `get_eids_def`
    (`cakeml/pancake/pan_to_crepScript.sml:346-353`).  Unlike
    `get_eids_from_decls`, this pass scans the exception identifiers reachable
    from function bodies, removes repeats in first-occurrence order, and only
    then assigns consecutive target words. -/
def pipelineExceptionIds (fromNat : Nat → α) : Nat → List ExceptionId → InfoMap α
  | _, [] => []
  | index, exception :: exceptions =>
      (exception, fromNat index) :: pipelineExceptionIds fromNat (index + 1) exceptions

def pipelineGetEids (fromNat : Nat → α) (functions : List (FunDecl α)) : InfoMap α :=
  pipelineExceptionIds fromNat 0
    ((functions.flatMap (fun function => expIds function.body)).eraseDups)

/-! Source-named port of the active CakeML Pancake
    `get_eids_from_decls_def` (`pan_to_crepScript.sml:356`).  Cake first
    filters to exception declarations, then numbers that filtered list from
    zero; the accumulator above expresses the same `MAP FST (exceptions ...)`
    and `GENLIST n2w` result without assigning IDs to ordinary declarations. -/
def crepGetEidsFromDecls (fromNat : Nat → α) (declarations : List (Decl α)) :
    InfoMap α :=
  pipelineExceptionCodes fromNat 0 declarations

/-! The exception-code table has exactly one entry for each declared
    exception.  This is the Lean counterpart of the size premise used by
    Cake's `get_eids_imp_excp_rel`: the table's finite-domain cardinality is
    fixed by the source declaration list, independently of the word map. -/
theorem pipelineExceptionCodes_length
    (fromNat : Nat → α) (index : Nat) (declarations : List (Decl α)) :
    (pipelineExceptionCodes fromNat index declarations).length =
      sizeOfEids declarations := by
  induction declarations generalizing index with
  | nil =>
      simp [pipelineExceptionCodes, sizeOfEids]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [pipelineExceptionCodes, sizeOfEids_cons, isExnDecl, ih] <;> omega

theorem crepGetEidsFromDecls_length
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    (crepGetEidsFromDecls fromNat declarations).length =
      sizeOfEids declarations := by
  exact pipelineExceptionCodes_length fromNat 0 declarations

/-- The exception-code table depends only on the exception declarations, so
    simplifying the function bodies with `pan_simp` leaves it unchanged.  This
    is the Flapjack counterpart of Cake's `get_eids_pan_simp_compile_eq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:105`), whose
    `FDOM (get_eids_from_decls prog)` is the finite-domain projection of
    `crepGetEidsFromDecls`. -/
theorem pipelineExceptionCodes_panSimpDecls (fromNat : Nat → α) (index : Nat)
    (declarations : List (Decl α)) :
    pipelineExceptionCodes fromNat index (panSimpDecls declarations) =
      pipelineExceptionCodes fromNat index declarations := by
  rw [panSimpDecls_eq_map]
  induction declarations generalizing index with
  | nil => simp [pipelineExceptionCodes]
  | cons declaration declarations ih =>
      cases declaration <;> simp [panSimpDecl, pipelineExceptionCodes, ih]

theorem crepGetEidsFromDecls_panSimpDecls (fromNat : Nat → α)
    (declarations : List (Decl α)) :
    crepGetEidsFromDecls fromNat (panSimpDecls declarations) =
      crepGetEidsFromDecls fromNat declarations :=
  pipelineExceptionCodes_panSimpDecls fromNat 0 declarations

/-! Cake's `get_eids_imp_excp_rel` begins by proving that every declared
    exception has a target code.  This constructive lookup half is useful at
    the generic Raise boundary: the exception-code premise is obtained from
    the source declaration table rather than guessed by an evaluator wrapper. -/
theorem crepGetEidsFromDecls_lookup_of_exception
    [BEq String] [LawfulBEq String]
    (fromNat : Nat → α) (index : Nat) :
    ∀ (declarations : List (Decl α)) (exception : ExceptionId) (shape : Shape),
      (exception, shape) ∈ exceptionEntries declarations →
      ∃ code, lookupInfo exception
        (pipelineExceptionCodes fromNat index declarations) = some code := by
  intro declarations
  induction declarations generalizing index with
  | nil =>
      intro exception shape hmem
      simp [exceptionEntries] at hmem
  | cons declaration declarations ih =>
      cases declaration with
      | exnDecl declaredException declaredShape =>
          intro exception shape hmem
          by_cases heq : exception == declaredException
          · have heq' : exception = declaredException := eq_of_beq heq
            subst exception
            exact ⟨fromNat index, by simp [pipelineExceptionCodes, lookupInfo]⟩
          · have htail : (exception, shape) ∈ exceptionEntries declarations := by
              have hmem' :
                  (exception = declaredException ∧ shape = declaredShape) ∨
                    (exception, shape) ∈ exceptionEntries declarations := by
                simpa [exceptionEntries] using hmem
              rcases hmem' with ⟨hname, _⟩ | htail
              · exfalso
                apply heq
                simp [hname]
              · exact htail
            have hne : (declaredException == exception) = false := by
              rw [Bool.eq_false_iff]
              intro h
              apply heq
              exact beq_iff_eq.mpr (eq_of_beq h).symm
            obtain ⟨code, hcode⟩ := ih (index + 1) exception shape htail
            exact ⟨code, by simp [pipelineExceptionCodes, lookupInfo, hne, hcode]⟩
      | decl declaredShape name value =>
          intro exception shape hmem
          exact ih index exception shape (by simpa [exceptionEntries] using hmem)
      | function declaration =>
          intro exception shape hmem
          exact ih index exception shape (by simpa [exceptionEntries] using hmem)
      | name struct fields =>
          intro exception shape hmem
          exact ih index exception shape (by simpa [exceptionEntries] using hmem)

/-! The finite-domain half of Cake get_eids_imp_excp_rel: the generated exception-code table has a lookup exactly when the source declaration list contains that exception. The code value remains abstract, matching Cake separate word-size and code-assignment premises. -/
theorem crepGetEidsFromDecls_lookup_iff_exception
    [BEq String] [LawfulBEq String]
    (fromNat : Nat → α) (index : Nat) :
    ∀ (declarations : List (Decl α)) (exception : ExceptionId),
      (∃ shape, (exception, shape) ∈ exceptionEntries declarations) ↔
        ∃ code, lookupInfo exception
          (pipelineExceptionCodes fromNat index declarations) = some code := by
  intro declarations
  induction declarations generalizing index with
  | nil =>
      intro exception
      simp [exceptionEntries, pipelineExceptionCodes, lookupInfo]
  | cons declaration declarations ih =>
      cases declaration with
      | exnDecl declaredException declaredShape =>
          intro exception
          by_cases heq : exception == declaredException
          · have heqEq : exception = declaredException := eq_of_beq heq
            subst exception
            simp [exceptionEntries, pipelineExceptionCodes, lookupInfo]
          · have hneq : exception ≠ declaredException := by
              intro h
              apply heq
              simp [h]
            have hne : (declaredException == exception) = false := by
              rw [Bool.eq_false_iff]
              intro h
              apply heq
              exact beq_iff_eq.mpr (eq_of_beq h).symm
            simpa [exceptionEntries, pipelineExceptionCodes, lookupInfo, heq, hne, hneq] using
              (ih (index + 1) exception)
      | decl declaredShape name value =>
          intro exception
          simpa [exceptionEntries, pipelineExceptionCodes, lookupInfo] using
            (ih index exception)
      | function declaration =>
          intro exception
          simpa [exceptionEntries, pipelineExceptionCodes, lookupInfo] using
            (ih index exception)
      | name struct fields =>
          intro exception
          simpa [exceptionEntries, pipelineExceptionCodes, lookupInfo] using
            (ih index exception)

def pipelineInlineNames : List (Decl α) → List FunName
  | [] => []
  | .function declaration :: declarations =>
      if declaration.inline then
        declaration.name :: pipelineInlineNames declarations
      else pipelineInlineNames declarations
  | _ :: declarations => pipelineInlineNames declarations
termination_by declarations => sizeOf declarations

/-! Faithful port of `pan_to_crep$compile_prog` from
    `cakeml/pancake/pan_to_crepScript.sml:393-398`.

    The source first builds the Crep table and then applies the inline pass to
    exactly the names of declarations marked `inlinable`; the callee body is
    recursively inlined before being spliced in (`crep_inlineScript.sml:215`). -/
def compileProgToCrep [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    List (CompiledFunction α) :=
  panToCrepCompileInlTop (pipelineInlineNames declarations)
    (compileToCrep context declarations)

/-! Cake's `first_compile_prog_all_distinct`
    (`pan_to_crepProofScript.sml:4556-4564`) at the complete
    `compile_prog` boundary.  The source declaration-name invariant first
    applies to `compile_to_crep`; the inline pass then preserves that table
    invariant because it changes only function bodies. -/
theorem compileProgToCrep_names_nodup
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (hnodup : (functionDeclarationNames declarations).Nodup) :
    (compileProgToCrep context declarations).map CompiledFunction.name |>.Nodup := by
  unfold compileProgToCrep
  apply panToCrepCompileInlTop_names_nodup
  exact compileToCrep_names_nodup context declarations hnodup

/-! Source-facing form of Cake's `first_compile_prog_all_distinct`: the
    distinctness premise is stated on the filtered function projection and
    the result includes the complete inline boundary. -/
theorem compileProgToCrep_names_nodup_of_functionDeclarations
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (hnodup : ((functionDeclarations declarations).map
      (fun declaration => declaration.name)).Nodup) :
    (compileProgToCrep context declarations).map CompiledFunction.name |>.Nodup := by
  unfold compileProgToCrep
  apply panToCrepCompileInlTop_names_nodup
  exact compileToCrep_names_nodup_of_functionDeclarations context declarations hnodup

/-! Cake's `compile_prog_distinct_params` at the complete source-shaped
    `compile_prog` boundary.  The pre-inline parameter invariant is supplied
    by `compileToCrep_params_nodup`; the inline pass preserves each record's
    parameter field. -/
theorem compileProgToCrep_params_nodup
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    ∀ function ∈ compileProgToCrep context declarations,
      function.params.Nodup := by
  unfold compileProgToCrep
  apply panToCrepCompileInlTop_params_nodup
  exact compileToCrep_params_nodup _ _

def pipelineFindFunction (name : FunName) :
    List (Decl α) → Option (FunDecl α)
  | [] => none
  | .function declaration :: declarations =>
      if declaration.name == name then some declaration
      else pipelineFindFunction name declarations
  | _ :: declarations => pipelineFindFunction name declarations
termination_by declarations => sizeOf declarations

/-! `pan_to_target_all` first moves the requested entry declaration to the
    front of the Pancake list (`pan_passesScript.sml:20-37`).  Keeping this
    source-order operation explicit is important because the linked section
    order is observable in the RISC-V artifact. -/
def panTargetMoveStartToFront [BEq String]
    (start : FunName) (declarations : List (Decl α)) : List (Decl α) :=
  globalDeclsFilter (fun declaration =>
      match declaration with
      | .function function => function.name == start
      | _ => false) declarations ++
    globalDeclsFilter (fun declaration =>
      match declaration with
      | .function function => function.name != start
      | _ => true) declarations

/-! Source-shaped port of CakeML Pancake's `exports_def`
    (`cakeml/pancake/pan_to_targetScript.sml:10`).  Export collection walks
    declarations in source order, keeps only exported functions, and ignores
    globals, exceptions, and structure declarations.  Keeping this as a
    separate executable helper preserves the observable export list without
    changing the target section ordering. -/
def panTargetExports : List (Decl α) → List FunName
  | [] => []
  | .function declaration :: declarations =>
      if declaration.exported then
        declaration.name :: panTargetExports declarations
      else
        panTargetExports declarations
  | _ :: declarations => panTargetExports declarations
termination_by declarations => sizeOf declarations

def pipelineCrepeContext [BEq α] [Add α]
    (bytesInWord : α) (fromNat : Nat → α)
    (program : GlobalCompiledProgram α) : CompileContext α :=
  { vars := []
    functions := []
    exceptions := crepGetEidsFromDecls fromNat program.declarations
    maxVar := 0
    bytesInWord := bytesInWord }

def pipelineCrepeCompileContext [BEq α] [Add α]
    (fromNat : Nat → α) (program : GlobalCompiledProgram α) :
    PanToCrepHOLContext α :=
  { vars := FEMPTY
    funcs := FEMPTY
    eids := FUPDATE_LIST FEMPTY (crepGetEidsFromDecls fromNat program.declarations)
    vmax := 0 }

/-- The executed RV64 compiler context obtains Cake's fixed byte width from
    the word type, not a caller-controlled field. -/
theorem pipelineCrepeCompileContext_riscv64
    (fromNat : Nat → BitVec 64) (program : GlobalCompiledProgram (BitVec 64)) :
    compileExpHOL (pipelineCrepeCompileContext fromNat program) .bytesInWord =
      ([.const CrepBytesInWord.bytesInWord], .one) := by
  simp [compileExpHOL]

/-- The production RV64 context lowers a structured load at Cake's fixed
    byte stride. -/
theorem compileExp_load_pipelineRiscv64
    (fromNat : Nat → BitVec 64) (program : GlobalCompiledProgram (BitVec 64))
    (shape : Shape) (expression : Exp (BitVec 64)) (head : CrepExp (BitVec 64))
    (rest : List (CrepExp (BitVec 64))) (shape' : Shape)
    (hcompile : compileExpHOL (pipelineCrepeCompileContext fromNat program)
      expression = (head :: rest, shape')) :
    (compileExpHOL (pipelineCrepeCompileContext fromNat program)
        (.load shape expression)).1 =
      loadShapeBytes 0 (Shape.shapeSize shape) head :=
  by
    simp only [compileExpHOL, hcompile]
    exact loadShape_eq_loadShapeBytes_of_stride_eq _ _ _ _ rfl

/-! Source-named ports of CakeML Pancake's `first_name_def` and
    `make_funcs_def` (`crep_to_loopScript.sml:243-255`).  The executable
    pipeline also needs a caller-selected label base when runtime sections
    reserve labels before user functions, so the parameterized helper keeps
    Cake's consecutive numbering while allowing that established ABI base. -/
def crepFirstName : Nat := 64

def crepMakeFuncsAt (firstName : Nat) :
    List (CompiledFunction α) → InfoMap (Nat × Nat)
  | [] => []
  | function :: functions =>
      (function.name, (firstName, function.params.length)) ::
        crepMakeFuncsAt (firstName + 1) functions

def crepMakeFuncs :
    List (CompiledFunction α) → InfoMap (Nat × Nat) :=
  crepMakeFuncsAt crepFirstName

def pipelineFunctionInfos (firstLabel : Nat) :
    List (CompiledFunction α) → InfoMap (Nat × Nat) :=
  crepMakeFuncsAt firstLabel

/-- Cake's `distinct_funcs` (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:60`):
    the numeric label assigned to a function is injective on the function
    names, in the list-backed `InfoMap` representation. -/
def crepDistinctFuncs (functions : InfoMap (Nat × Nat)) : Prop :=
  ∀ (x y : FunName) (n m : Nat) (rm rm' : Nat),
    lookupInfo x functions = some (n, rm) →
    lookupInfo y functions = some (m, rm') → n = m → x = y

theorem crepMakeFuncsAt_label_ge (start : Nat)
    (functions : List (CompiledFunction α)) :
    ∀ {x : FunName} {n rm : Nat},
      lookupInfo x (crepMakeFuncsAt start functions) = some (n, rm) →
        start ≤ n := by
  induction functions generalizing start with
  | nil => intro x n rm h; simp [crepMakeFuncsAt, lookupInfo] at h
  | cons function functions ih =>
      intro x n rm h
      simp only [crepMakeFuncsAt, lookupInfo] at h
      by_cases hc : (function.name == x) = true
      · rw [if_pos hc] at h
        have hpair := Option.some.inj h
        have : start = n := congrArg Prod.fst hpair
        omega
      · rw [if_neg hc] at h
        have := ih (start := start + 1) h
        omega

theorem crepDistinctFuncs_crepMakeFuncsAt (start : Nat)
    (functions : List (CompiledFunction α)) :
    crepDistinctFuncs (crepMakeFuncsAt start functions) := by
  intro x y n m rm rm' hx hy hnm
  induction functions generalizing start with
  | nil => simp [crepMakeFuncsAt, lookupInfo] at hx
  | cons function functions ih =>
      simp only [crepMakeFuncsAt, lookupInfo] at hx hy
      by_cases hcx : (function.name == x) = true
      · rw [if_pos hcx] at hx
        have hxn : start = n := congrArg Prod.fst (Option.some.inj hx)
        by_cases hcy : (function.name == y) = true
        · rw [if_pos hcy] at hy
          have hxname : x = function.name := (beq_iff_eq.mp hcx).symm
          have hyname : y = function.name := (beq_iff_eq.mp hcy).symm
          exact hxname.trans hyname.symm
        · rw [if_neg hcy] at hy
          have hge := crepMakeFuncsAt_label_ge (start := start + 1) functions hy
          omega
      · rw [if_neg hcx] at hx
        by_cases hcy : (function.name == y) = true
        · rw [if_pos hcy] at hy
          have hyn : start = m := congrArg Prod.fst (Option.some.inj hy)
          have hge := crepMakeFuncsAt_label_ge (start := start + 1) functions hx
          omega
        · rw [if_neg hcy] at hy
          exact ih (start := start + 1) hx hy

/-- Cake's `distinct_make_funcs`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3757`): the function
    table built by `make_funcs` has distinct labels. -/
theorem crepDistinctFuncs_crepMakeFuncs (functions : List (CompiledFunction α)) :
    crepDistinctFuncs (crepMakeFuncs functions) :=
  crepDistinctFuncs_crepMakeFuncsAt crepFirstName functions

/-- Cake's `initial_prog_make_funcs_el`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3942`): the label a
    function receives from `make_funcs` identifies the position of that
    function in the source list.  CakeML writes the label of the `n`-th
    function as `n + first_name`; the list-backed Flapjack port instead
    inverts a successful lookup into the index whose label is
    `start + index`. -/
theorem crepMakeFuncsAt_exists_index (start : Nat)
    (functions : List (CompiledFunction α))
    {name : FunName} {label rm : Nat}
    (h : lookupInfo name (crepMakeFuncsAt start functions) = some (label, rm)) :
    ∃ n, label = start + n ∧
      (functions[n]?).map (fun function => function.name) = some name ∧
        n < functions.length := by
  induction functions generalizing start with
  | nil => simp [crepMakeFuncsAt, lookupInfo] at h
  | cons function functions ih =>
      simp only [crepMakeFuncsAt, lookupInfo] at h
      by_cases hc : (function.name == name) = true
      · rw [if_pos hc] at h
        have hlabel : label = start := (congrArg Prod.fst (Option.some.inj h)).symm
        exact ⟨0, by omega, by simp [beq_iff_eq.mp hc], by simp⟩
      · rw [if_neg hc] at h
        obtain ⟨n, hlabel, hget, hn⟩ := ih (start := start + 1) h
        refine ⟨n + 1, by omega, ?_, by simp; omega⟩
        simp only [List.getElem?_cons_succ]
        exact hget

/-- Cake's `initial_prog_make_funcs_el` for the `make_funcs` label base. -/
theorem crepMakeFuncs_exists_index (functions : List (CompiledFunction α))
    {name : FunName} {label rm : Nat}
    (h : lookupInfo name (crepMakeFuncs functions) = some (label, rm)) :
    ∃ n, label = crepFirstName + n ∧
      (functions[n]?).map (fun function => function.name) = some name ∧
        n < functions.length :=
  crepMakeFuncsAt_exists_index crepFirstName functions h

/-! Source-facing port of `crep_to_loop$compile_prog`.  Pancake's `comp_func`
    context sets `vmax = LENGTH params - 1`. -/
def pipelineLoopFunctionsSourceAux [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (functionInfos : InfoMap (Nat × Nat)) :
    Nat → List (CompiledFunction α) → List (Nat × List Nat × LoopProg α)
  | _, [] => []
  | label, function :: functions =>
      (label, List.range function.params.length,
        crepCompFunc architecture functionInfos function.params function.body) ::
        pipelineLoopFunctionsSourceAux architecture functionInfos (label + 1) functions

def pipelineLoopFunctionsSource [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (firstLabel : Nat)
    (functions : List (CompiledFunction α)) :
    List (Nat × List Nat × LoopProg α) :=
  pipelineLoopFunctionsSourceAux architecture (pipelineFunctionInfos firstLabel functions)
    firstLabel functions

/-! Source-facing port of `loop_to_word$compile_prog`.  CakeML rebuilds a
    dense even-register context from
    `params ++ fromNumSet (difference (acc_vars body) params)`.  Use that
    context for source-entry artifacts, including the identity lowering path;
    otherwise the identity path can disagree with the full-SSA fallback on
    programs whose assigned variables are sparse. -/
def pipelineWordFunctionsSource [OfNat α 1]
    (functions : List (Nat × List Nat × LoopProg α)) :
    List (Nat × List Nat × WordProg α) :=
  functions.map (fun (label, parameters, body) =>
    (label, LoopToWord.loopToWordCompParameters parameters body,
      wordProgDCE (LoopToWord.loopToWordCompFunc label parameters body)))

/-! Source-shaped `loop_to_word$compile_prog` output.  The ordinary pipeline
    keeps parameter names for later register allocation; `pan_to_word` instead
    exposes each function's source label, arity (including the entry slot), and
    compiled body. -/
def pipelineWordCompileProg [OfNat α 1]
    (functions : List (Nat × List Nat × LoopProg α)) :
    List (Nat × Nat × WordProg α) :=
  LoopToWord.loopToWordCompileProg functions

def panToWordCompileProg [OfNat α 1]
    (functions : List (Nat × List Nat × LoopProg α)) :
    List (Nat × Nat × WordProg α) :=
  pipelineWordCompileProg functions

/-! Full-SSA Lab sections use label 0 for their public entry and label 1 for
    the tail-sequence entry marker.  Handler labels are function-specific, so
    continuation labels must also start above every function label; otherwise
    a handler in the highest-numbered function can alias its call continuation.
    This helper computes that fresh lower bound from the generated functions. -/
def fullSsaInitialLabLabel : List (Nat × List Nat × StackProg Nat) → Nat
  | [] => 2
  | (label, _, _) :: functions =>
      max (label + 1) (fullSsaInitialLabLabel functions)

theorem lookupNatInfo_map_add_two_of_mem (slots : List Nat) (name : Nat)
    (hname : name ∈ slots) :
    lookupNatInfo name (slots.map (fun value => (value, value + 2))) =
      some (name + 2) := by
  induction slots with
  | nil => simp at hname
  | cons head tail ih =>
      simp only [List.mem_cons] at hname
      rcases hname with rfl | hname
      · simp [lookupNatInfo]
      · by_cases heq : head == name
        · have : head = name := by simpa using heq
          subst head
          simp [lookupNatInfo]
        · simp [lookupNatInfo, heq, ih hname]

def pipelineWordContext (slots : List Nat) : WordContext :=
  { vars := slots.map (fun name => (name, name + 2)) }

theorem wordFindVar_pipelineWordContext_of_mem (slots : List Nat) (name : Nat)
    (hname : name ∈ slots) :
    wordFindVar (pipelineWordContext slots) name = name + 2 := by
  simp [pipelineWordContext, wordFindVar,
    lookupNatInfo_map_add_two_of_mem slots name hname]

def pipelinePrependInitializers (initializers : List (Prog α)) :
    List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      if declaration.name = "main" then
        .function { declaration with body :=
          (.seq (nestedSeq initializers) declaration.body) } :: declarations
      else
        .function declaration :: pipelinePrependInitializers initializers declarations
  | declaration :: declarations =>
      declaration :: pipelinePrependInitializers initializers declarations

structure FlapjackPipelineResult (α : Type u) where
  simplified : List (Decl α)
  structured : List (Decl α)
  globals : GlobalCompiledProgram α
  crepe : List (CompiledFunction α)
  loop : List (Nat × List Nat × LoopProg α)
  word : List (Nat × List Nat × WordProg α)

/-! Typed output-boundary port of Cake's `pan_compile_tap_def`
    (`pan_passesScript.sml:668-674`).  The pass pipeline supplies the
    already-computed output and typed intermediate stages; this wrapper keeps
    Cake's exact explore-flag behavior and `pp_with_title` ordering. -/
def panCompileTapReports [CakeDisplayWord α]
    (stages : List (String × AnyPanProg α)) : List String :=
  match stages with
  | [] => []
  | (title, stage) :: stages =>
      ["# ", title, "\n\n"] ++ anyPanProgPp stage ++
        panCompileTapReports stages

def panCompileTap [CakeDisplayWord α]
    (exploreFlag : Bool) (output : β)
    (stages : List (String × AnyPanProg α)) : β × List String :=
  if exploreFlag then
    (output, panCompileTapReports stages)
  else
    (output, [])

/-! Source-facing Pancake compiler entry point. This executes the fixed-interface
    `globalCompileTopCake` result at the global pass boundary.  The remaining
    metadata is retained from `globalCompileTop` for callers that inspect the
    intermediate pipeline record; the declarations sent into Crep are the
    direct output of Cake's tagged `compile_top`.

    The production `compile_prog` call below remains on the String-backed
    implementation. `compileProgTopHOLOfExact` is currently only a carrier
    adapter: it decodes `DeclHOL` back into production declarations before
    calling that same source-shaped implementation, and the reverse codec is
    lossy for names outside `NameRanged`. `parseTopDecs_declByteRanged` proves
    the parser result is in range, but that proof is not yet propagated through
    move-start, simplification, struct compilation, and `globalCompileTopCake`.
    Until that pass invariant is proved, routing this general pipeline API
    through the adapter would silently change results for arbitrary production
    declarations. The missing global-pass invariant is tracked by
    `flapjack-pxn.18.3.5.8.7.1.2.1`; the faithful exact `compile_prog` port is
    tracked by `flapjack-pxn.18.3.5.8.13`. Neither is claimed complete here. -/
def compileFlapjackEntryCake {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1] [Add (BitVec width)] [Mul (BitVec width)]
    [AndOp (BitVec width)] [ShiftRight (BitVec width)]
    [PanShiftWidth (BitVec width)]
    (architecture : RiscV.Architecture) (bytesInWord : BitVec width)
    (fromNat : Nat → BitVec width) (start : FunName)
    (declarations : List (Decl (BitVec width))) :
    Option (FlapjackPipelineResult (BitVec width)) :=
  let declarations := panTargetMoveStartToFront start declarations
  let simplified := panSimpDecls declarations
  let structured := structCompileTop simplified
  let cakeDeclarations := globalCompileTopCake structured start
  match cakeDeclarations with
  | [] => none
  | _ :: _ =>
      let renamed := globalNewMainName structured
      let prepared := globalRenameDecls start renamed (globalResortDecls structured)
      let metadata := globalCompileTop bytesInWord fromNat prepared
      let globals := { metadata with declarations := cakeDeclarations }
      let crepe := crepSimpFunctions fromNat
        (compileProgTopHOLWithMetadata cakeDeclarations)
      let loop := pipelineLoopFunctionsSource architecture 1 crepe
      let word := pipelineWordFunctionsSource loop
      some (FlapjackPipelineResult.mk simplified structured globals crepe loop word)

/-! Executable mirror of the missing-`main` branch of `pan_to_target_all`
    (`cakeml/pancake/pan_passesScript.sml:20-37`): when the program has no
    `main` declaration the original synthesizes `main = «return 0»` and
    prepends it before running the remaining passes. -/
def panTargetDeclarationsWithDefaultMain [OfNat α 0] [OfNat α 1]
    (declarations : List (Decl α)) : List (Decl α) :=
  if declarations.any (fun declaration =>
      match declaration with
      | .function function => function.name == "main"
      | _ => false) then
    declarations
  else match declarations with
    | [] => []
    | _ =>
      .function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one } :: declarations

end Flapjack
