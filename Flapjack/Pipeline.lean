import Flapjack.PanGlobals
import Flapjack.Compile
import Flapjack.CompileFunctionDistinct
import Flapjack.CrepeInlinePass
import Flapjack.CrepeArith
import Flapjack.CrepToLoop
import Flapjack.CrepToLoopOptimise
import Flapjack.LoopToWord
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
        simp [pipelineExceptionCodes, sizeOfEids, isExnDecl, ih] <;> omega

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

def pipelineLoopFunctionsAux [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (functionInfos : InfoMap (Nat × Nat)) :
    Nat → List (CompiledFunction α) → List (Nat × List Nat × LoopProg α)
  | _, [] => []
  | label, function :: functions =>
      let context : LoopContext α :=
        crepMkCtxt architecture [] functionInfos function.params.length
      (label, function.params, oCompile context function.params function.body) ::
        pipelineLoopFunctionsAux architecture functionInfos (label + 1) functions

def pipelineLoopFunctions [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (firstLabel : Nat)
    (functions : List (CompiledFunction α)) :
    List (Nat × List Nat × LoopProg α) :=
  pipelineLoopFunctionsAux architecture (pipelineFunctionInfos firstLabel functions)
    firstLabel functions

/-! Source-facing counterpart of `crep_to_loop$compile_prog`.  The historical
    `pipelineLoopFunctions` above is retained for the earlier correctness
    witnesses whose register numbering is part of their checked shape.  The
    Pancake source pipeline uses `comp_func`, whose context sets
    `vmax = LENGTH params - 1`; this separate entry point keeps that rule
    explicit without changing the legacy API. -/
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

def pipelineWordFunctions [OfNat α 1]
    (functions : List (Nat × List Nat × LoopProg α)) :
    List (Nat × List Nat × WordProg α) :=
  functions.map (fun (label, parameters, body) =>
    let slots := loopAccVars body parameters
    let context : WordContext :=
      { vars := slots.map (fun name => (name, name + 2)) }
    (label, parameters.map (fun name => name + 2),
      wordProgDCE (loopToWordProg context body)))

/-! Source-facing counterpart of `pipelineWordFunctions`.  The ordinary
    helper above predates the executable `loop_to_word$comp_func` port and
    assumes that every source variable keeps its numeric name after adding
    two.  CakeML instead rebuilds a dense even-register context from
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

/-! StackLang view of the register-coloured Word pipeline.  This is the
    executable bridge used by the RISC-V-only backend path below; functions
    that require spills or unsupported Word constructors remain explicit
    `none` results until those allocator cases are ported. -/
def pipelineWordFunctionsToStack [NeZero width] :
    List (Nat × List Nat × WordProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let config := { RiscV.wordStackIdentityConfig body with
        sectionId := label
        handlerLabel := label }
      let stackBody ← RiscV.wordToStackProgWord config body
      let rest ← pipelineWordFunctionsToStack functions
      pure ((label, parameters, stackBody) :: rest)

/-! The allocator-aware counterpart of `pipelineWordFunctionsToStack`.  The
    coloured Word program uses concrete register names, so the StackLang
    boundary can use the same identity location map while still rejecting
    programs that the allocator cannot colour. -/
def pipelineAllocatedWordFunctionsToStack [NeZero width] :
    List (Nat × List Nat × WordProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat)) :=
  pipelineWordFunctionsToStack

/-! Spill-aware allocator pipeline.  This path retains the SSA-renamed Word
    program and passes the CakeML-shaped clash-tree/preference allocator's
    concrete register/stack locations directly to `word_to_stack`.  The
    reserved x31 scratch register is outside the allocator's register pool,
    and x29 is reserved independently for spilled addresses. -/
def pipelineWordFunctionsAllocatedWithSpills [NeZero width] :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let context : WordContext :=
        { vars := slots.map (fun name => (name, name + 2)) }
      let wordParameters := parameters.map (fun name => name + 2)
      let unallocatedBody :=
        RiscV.wordFlattenProgramFrom (loopToWordProg context body)
      let (_, renamedParameters, renamedBody, allocation) ←
        wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
          wordParameters unallocatedBody
      let config : RiscV.WordStackConfig :=
        { locations := allocation.locations
          scratch := 31
          stackBase := 0
          addressScratch := 29
          abiBase := 10
          abiStride := 1
          sectionId := label
          handlerLabel := label }
      /- CakeML's spill path carries allocator-owned heap operations through
         the bitmap-threaded word_to_stack compiler.  Keep the historical
         flat result shape here, but do not fall back to the stateless wrapper:
         that wrapper deliberately rejects Alloc and StoreConsts. -/
      let (stackBody, _) ←
        RiscV.wordToStackFunctionWithParametersAndLocationBitmaps config
          renamedParameters wordAllocatableRegisters.length config.scratch
          allocation.nextSpill (some 1)
          (RiscV.wordStackInitialBitmaps false) renamedBody
      let rest ← pipelineWordFunctionsAllocatedWithSpills functions
      pure ((label, wordParameters, stackBody) :: rest)

/-! Spill-aware pipeline with CakeML's append-only bitmap state.  The
    location-aware Word-to-Stack boundary derives GC roots from the concrete
    spill slots produced by the allocator and carries the updated bitmap
    table into the next function. -/
def pipelineWordFunctionAllocatedWithSpillsAndBitmaps [NeZero width]
    (bitmaps : RiscV.WordStackBitmapState)
    (function : Nat × List Nat × LoopProg (RiscV.Word width)) :
    Option ((Nat × List Nat × StackProg Nat) × RiscV.WordStackBitmapState) :=
  let (label, parameters, body) := function
  do
    let slots := loopAccVars body parameters
    let context : WordContext :=
      { vars := slots.map (fun name => (name, name + 2)) }
    let wordParameters := parameters.map (fun name => name + 2)
    let unallocatedBody := RiscV.wordFlattenProgramFrom (loopToWordProg context body)
    let (_, renamedParameters, renamedBody, allocation) ←
      wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
        wordParameters unallocatedBody
    let config : RiscV.WordStackConfig :=
      { locations := allocation.locations
        scratch := 31
        stackBase := 0
        addressScratch := 29
        abiBase := 10
        abiStride := 1
        sectionId := label
        handlerLabel := label }
    let (stackBody, bitmaps) ←
      RiscV.wordToStackFunctionWithParametersAndLocationBitmaps config
        renamedParameters wordAllocatableRegisters.length config.scratch
        allocation.nextSpill (some 1) bitmaps renamedBody
    pure ((label, wordParameters, stackBody), bitmaps)

def pipelineWordFunctionsAllocatedWithSpillsAndBitmaps [NeZero width]
    (bitmaps : RiscV.WordStackBitmapState) :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option
        (List (Nat × List Nat × StackProg Nat) × RiscV.WordStackBitmapState)
  | [] => some ([], bitmaps)
  | function :: functions => do
      let (compiled, bitmaps) ←
        pipelineWordFunctionAllocatedWithSpillsAndBitmaps bitmaps function
      let (rest, bitmaps) ←
        pipelineWordFunctionsAllocatedWithSpillsAndBitmaps bitmaps functions
      pure (compiled :: rest, bitmaps)

/-! The bitmap accumulator is threaded through function compilation in source
    order.  This equation makes that sequencing explicit for callers that
    split a declaration list into independently compiled chunks. -/
theorem pipelineWordFunctionsAllocatedWithSpillsAndBitmaps_append [NeZero width]
    (bitmaps : RiscV.WordStackBitmapState)
    (first second : List (Nat × List Nat × LoopProg (RiscV.Word width))) :
    pipelineWordFunctionsAllocatedWithSpillsAndBitmaps bitmaps (first ++ second) =
      match pipelineWordFunctionsAllocatedWithSpillsAndBitmaps bitmaps first with
      | none => none
      | some (firstCode, middleBitmaps) =>
          match pipelineWordFunctionsAllocatedWithSpillsAndBitmaps middleBitmaps second with
          | none => none
          | some (secondCode, finalBitmaps) =>
              some (firstCode ++ secondCode, finalBitmaps) := by
  induction first generalizing bitmaps with
  | nil =>
      cases hsecond : pipelineWordFunctionsAllocatedWithSpillsAndBitmaps bitmaps second <;>
        simp [pipelineWordFunctionsAllocatedWithSpillsAndBitmaps, hsecond]
  | cons function functions ih =>
      cases hfunction : pipelineWordFunctionAllocatedWithSpillsAndBitmaps bitmaps function with
      | none => simp [pipelineWordFunctionsAllocatedWithSpillsAndBitmaps, hfunction]
      | some compiled =>
          cases hrest : pipelineWordFunctionsAllocatedWithSpillsAndBitmaps compiled.2 functions with
          | none =>
              have htail := ih (bitmaps := compiled.2)
              simp [pipelineWordFunctionsAllocatedWithSpillsAndBitmaps, hfunction, hrest, htail]
          | some rest =>
              cases hsecond : pipelineWordFunctionsAllocatedWithSpillsAndBitmaps rest.2 second <;>
                simp [pipelineWordFunctionsAllocatedWithSpillsAndBitmaps, hfunction, hrest,
                  hsecond, ih compiled.2]

/-! Bitmap-carrying spill pipeline using the complete CakeML-shaped SSA
    function entry.  Unlike the historical bitmap path above, this variant
    allocates the explicit formal-parameter moves together with the renamed
    body and feeds the same location map to the state-threaded
    Word-to-Stack compiler. -/

def pipelineWordFunctionAllocatedWithSpillsAndFullSsaAndBitmaps [NeZero width]
    (bitmaps : RiscV.WordStackBitmapState)
    (function : Nat × List Nat × LoopProg (RiscV.Word width)) :
    Option ((Nat × List Nat × StackProg Nat) × RiscV.WordStackBitmapState) :=
  let (label, parameters, body) := function
  do
    let slots := loopAccVars body parameters
    let context : WordContext :=
      { vars := slots.map (fun name => (name, name + 2)) }
    let wordParameters := parameters.map (fun name => name + 2)
    let unallocatedBody := RiscV.wordFlattenProgramFrom (loopToWordProg context body)
    let (_, renamedParameters, renamedProgram, allocation) ←
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixedClashFast
        wordParameters unallocatedBody
    let config : RiscV.WordStackConfig :=
      { locations := allocation.locations
        scratch := 31
        stackBase := 0
        addressScratch := 29
        abiBase := 10
        abiStride := 1
        sectionId := label
        handlerLabel := label }
    let lower :=
      if !RiscV.wordProgNeedsCakeFrame renamedProgram then
        RiscV.wordToStackFunctionWithParametersAndLocationBitmaps config
          renamedParameters wordAllocatableRegisters.length config.scratch
          allocation.nextSpill (some 1) bitmaps renamedProgram
      else
        RiscV.wordToStackFunctionWithCakeFrameAndLocationBitmaps config
          renamedParameters wordAllocatableRegisters.length config.scratch
          allocation.nextSpill (some 1) bitmaps renamedProgram
    let (stackBody, bitmaps) ← lower
    pure ((label, wordParameters, stackBody), bitmaps)

def pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps [NeZero width]
    (bitmaps : RiscV.WordStackBitmapState) :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option
        (List (Nat × List Nat × StackProg Nat) × RiscV.WordStackBitmapState)
  | [] => some ([], bitmaps)
  | function :: functions => do
      let (compiled, bitmaps) ←
        pipelineWordFunctionAllocatedWithSpillsAndFullSsaAndBitmaps bitmaps function
      let (rest, bitmaps) ←
        pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps bitmaps functions
      pure (compiled :: rest, bitmaps)

theorem pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps_append
    [NeZero width] (bitmaps : RiscV.WordStackBitmapState)
    (first second : List (Nat × List Nat × LoopProg (RiscV.Word width))) :
    pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps bitmaps
        (first ++ second) =
      match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
          bitmaps first with
      | none => none
      | some (firstCode, middleBitmaps) =>
          match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
              middleBitmaps second with
          | none => none
          | some (secondCode, finalBitmaps) =>
              some (firstCode ++ secondCode, finalBitmaps) := by
  induction first generalizing bitmaps with
  | nil =>
      cases hsecond :
          pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
            bitmaps second <;>
        simp [pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps,
          hsecond]
  | cons function functions ih =>
      cases hfunction :
          pipelineWordFunctionAllocatedWithSpillsAndFullSsaAndBitmaps
            bitmaps function with
      | none =>
          simp [pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps,
            hfunction]
      | some compiled =>
          cases hrest :
              pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
                compiled.2 functions with
          | none =>
              have htail := ih (bitmaps := compiled.2)
              simp [pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps,
                hfunction, hrest, htail]
          | some rest =>
              cases hsecond :
                  pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
                    rest.2 second <;>
                simp [pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps,
                  hfunction, hrest, hsecond, ih compiled.2]

/-! Graph-coloured Word-to-Stack pipeline.

This is the first pipeline entry point that consumes the CakeML-shaped graph
allocator rather than the earlier greedy spill allocator.  The allocator
returns the SSA-renamed program together with its graph; `wordGraphLocations`
then turns the graph colours into the register/stack locations expected by
`word_to_stack`.  The old spill path remains available while the full
spill-aware SSA metadata and all Word constructors are being ported.
-/
def pipelineWordFunctionsAllocatedWithGraph [NeZero width] :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let context : WordContext :=
        { vars := slots.map (fun name => (name, name + 2)) }
      let wordParameters := parameters.map (fun name => name + 2)
      let unallocatedBody := RiscV.wordFlattenProgramFrom (loopToWordProg context body)
      let (_, renamedParameters, allocation, renamedBody) ←
        wordAllocateGraphFunctionWithStackOnlyPrefreezeRenamed wordParameters unallocatedBody
          [] 13 14
      let config : RiscV.WordStackConfig :=
        { locations := wordGraphLocations allocation 13 14
          scratch := 31
          stackBase := 0
          addressScratch := 29
          abiBase := 10
          abiStride := 1
          sectionId := label
          handlerLabel := label }
      let stackBody ← RiscV.wordToStackFunctionWithParameters config
        renamedParameters renamedBody
      let rest ← pipelineWordFunctionsAllocatedWithGraph functions
      pure ((label, wordParameters, stackBody) :: rest)

/-! Graph-backed pipeline variant using CakeML's complete SSA function entry.
    The source ABI names are fixed in the graph allocator, while the returned
    SSA names remain available to the parameter-move lowering. -/
def pipelineWordFunctionsAllocatedWithGraphAndFullSsa [NeZero width] :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let context : WordContext :=
        { vars := slots.map (fun name => (name, name + 2)) }
      let wordParameters := parameters.map (fun name => name + 2)
      let unallocatedBody := RiscV.wordFlattenProgramFrom (loopToWordProg context body)
      let (_, renamedParameters, allocation, renamedProgram) ←
        wordAllocateGraphFunctionWithEntryPrefreezeRenamed wordParameters unallocatedBody
          wordParameters 13 14
      let config : RiscV.WordStackConfig :=
        { locations := wordGraphLocations allocation 13 14
          scratch := 31
          stackBase := 0
          addressScratch := 29
          abiBase := 10
          abiStride := 1
          sectionId := label
          handlerLabel := label }
      let stackBody ← RiscV.wordToStackFunctionWithParameters config
        renamedParameters renamedProgram
      let rest ← pipelineWordFunctionsAllocatedWithGraphAndFullSsa functions
      pure ((label, wordParameters, stackBody) :: rest)

/-! Spill-backed pipeline variant using the ABI-correct full-SSA entry
    allocator.  The generated entry moves therefore read the same physical
    argument registers that the location-aware Word-to-Stack lowering
    initializes.  This legacy flat-code API discards the bitmap artifact, but
    still uses the state-threaded lowering so full-SSA `Alloc` and
    `StoreConsts` constructors are not rejected by the old stateless path. -/
def pipelineWordFunctionsAllocatedWithSpillsAndFullSsa [NeZero width] :
    List (Nat × List Nat × LoopProg (RiscV.Word width)) →
      Option (List (Nat × List Nat × StackProg Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let wordParameters := wordSsaAbiParameters parameters.length
      /- Cake's `word_to_word` pipeline keeps the selected Word program intact
         through full SSA.  In particular, `word_unreach` runs after SSA and
         the cleanup/CSE passes; removing an unreachable tail here changes
         `max_var`, and therefore the fresh SSA names and final RISC-V bytes. -/
      let unallocatedBody :=
        RiscV.wordInstSelectProgramFrom
          (RiscV.wordToWordPreSsa
            (RiscV.wordFlattenProgramFrom
              (LoopToWord.loopToWordCompFunc label parameters body)))
      let (_, renamedParameters, renamedProgram, allocation) ←
        RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead label wordParameters
          unallocatedBody
      let frameSlots := max allocation.nextSpill
        (wordParameters.length - RiscV.CakeRegAlloc.cakeRiscVRegisterCount)
      let config : RiscV.WordStackConfig :=
        { locations := allocation.locations
          scratch := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
          stackBase := 0
          addressScratch := 29
          abiBase := 1
          abiStride := 1
          abiFrameSlots := frameSlots
          sectionId := label
          handlerLabel := label }
      let lower :=
        if frameSlots = 0 then
          RiscV.wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMoves config
            renamedParameters RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
            frameSlots (some 1) (RiscV.wordStackInitialBitmaps false) renamedProgram
        else
          RiscV.wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMoves config
            renamedParameters RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
            frameSlots (some 1) (RiscV.wordStackInitialBitmaps false) renamedProgram
      let (stackBody, _) ← lower
      let rest ← pipelineWordFunctionsAllocatedWithSpillsAndFullSsa functions
      pure ((label, wordParameters, stackBody) :: rest)

/-! Full-SSA Lab sections use label 0 for their public entry and label 1 for
    the tail-sequence entry marker.  Handler labels are function-specific, so
    continuation labels must also start above every function label; otherwise
    a handler in the highest-numbered function can alias its call continuation.
    This helper computes that fresh lower bound from the generated functions. -/
def fullSsaInitialLabLabel : List (Nat × List Nat × StackProg Nat) → Nat
  | [] => 2
  | (label, _, _) :: functions =>
      max (label + 1) (fullSsaInitialLabLabel functions)

/-!
An allocation-aware variant of the Word-function boundary.  The historical
`pipelineWordFunctions` definition remains available for existing artifact
equations; this variant makes register exhaustion explicit and uses the
reserved-register-aware allocator before instruction selection.
-/
def pipelineWordFunctionsAllocated [OfNat α 1]
    : List (Nat × List Nat × LoopProg α) →
      Option (List (Nat × List Nat × WordProg α))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let context ← wordAllocateContext slots
      let rest ← pipelineWordFunctionsAllocated functions
      pure ((label, wordMapVars context parameters, loopToWordProg context body) :: rest)

/-! Allocation-aware variant that derives clashes from the generated Word
program.  It is still separate from the historical artifact boundary while
the full CakeML branch/loop SSA and spill pass are being ported. -/
def pipelineWordFunctionsAllocatedWithAnalysis [OfNat α 1]
    : List (Nat × List Nat × LoopProg α) →
      Option (List (Nat × List Nat × WordProg α))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let unallocatedBody := loopToWordProg ({ vars := [] } : WordContext) body
      let context ← wordAllocateProgramWithSlots slots unallocatedBody
      let rest ← pipelineWordFunctionsAllocatedWithAnalysis functions
      pure ((label, wordMapVars context parameters, loopToWordProg context body) :: rest)

/-! Variant that consumes the same analysis boundary but returns the coloured
    Word program directly.  This is the form expected by the target selector;
    the context is retained alongside the code for later state-relation proofs. -/
def pipelineWordFunctionsAllocatedWithAnalysisAndColour [OfNat α 1]
    : List (Nat × List Nat × LoopProg α) →
      Option (List (Nat × List Nat × WordProg α))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let slots := loopAccVars body parameters
      let unallocatedBody := loopToWordProg ({ vars := [] } : WordContext) body
      let (context, allocatedBody) ←
        wordAllocateProgramWithSlotsAndColour slots unallocatedBody
      let rest ← pipelineWordFunctionsAllocatedWithAnalysisAndColour functions
      pure ((label, wordMapVars context parameters, allocatedBody) :: rest)

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

def pipelineRiscVFunctions [NeZero width]
    (functions : List (Nat × List Nat × WordProg (RiscV.Word width))) :
    List (Nat × List Nat × Option (List (RiscV.Instruction width) × List (Fin 32))) :=
  functions.map (fun (label, parameters, body) =>
    (label, parameters, RiscV.wordFunctionToRiscVWithLoops body))

def pipelineRiscVFunctionsWithFfi [NeZero width]
    (services : List (FunName × Nat))
    (functions : List (Nat × List Nat × WordProg (RiscV.Word width))) :
    List (Nat × List Nat × Option (List (RiscV.Instruction width) × List (Fin 32))) :=
  let targets := match RiscV.wordFunctionTargetSignaturesWithCalls functions with
    | some targets => targets
    | none => []
  let context : RiscV.WordCallFfiContext width :=
    { targets := targets, services := services }
  functions.map (fun (label, parameters, body) =>
    (label, parameters,
      RiscV.wordFunctionToRiscVWithCallsAndFfiAndLoops context body))

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

/-! The pass-local core used when the target wrapper cannot be constructed (in
    particular for an empty declaration list).  The public `compileFlapjack`
    below goes through `compileFlapjackTarget`, matching Cake's
    initializer-wrapper path; keeping this core named prevents the target
    fallback from recursively calling the public entry point. -/
def compileFlapjackCore [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [AndOp α] [ShiftRight α] [PanShiftWidth α]
    (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    FlapjackPipelineResult α :=
  let simplified := panSimpDecls declarations
  let structured := structCompileTop simplified
  let globals := globalCompileTop bytesInWord fromNat structured
  let crepeContext := pipelineCrepeContext bytesInWord fromNat globals
  let declarations := pipelinePrependInitializers globals.initializers globals.declarations
  let compiled := compileToCrep crepeContext declarations
  let crepe := crepSimpFunctions fromNat
    (crepInlineTopRecursiveByNames (pipelineInlineNames declarations) compiled)
  let loop := pipelineLoopFunctions architecture 1 crepe
  let word := pipelineWordFunctions loop
  { simplified := simplified
    structured := structured
    globals := globals
    crepe := crepe
    loop := loop
    word := word }

/-! Exact `pan_to_target` entry preparation.  The ordinary pipeline above is
    retained for pass-local fixtures.  This entry-point form follows CakeML: it
    moves the requested source function to the front of the program (the
    SPLITP permutation above), finds it, gives it a fresh name, permutes all
    function references, and emits a new public `main` whose body runs global
    initializers before a tail call to the renamed source entry. -/
def compileFlapjackEntry [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [AndOp α] [ShiftRight α] [PanShiftWidth α]
    (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (start : FunName) (declarations : List (Decl α)) :
    Option (FlapjackPipelineResult α) :=
  let declarations := panTargetMoveStartToFront start declarations
  let simplified := panSimpDecls declarations
  let structured := structCompileTop simplified
  match pipelineFindFunction start structured with
  | none => none
  | some entry =>
      /- CakeML's `compile_top` always freshens the literal `main`, not the
         `start` parameter (`pan_globalsScript.sml:224-226,242`). -/
      let renamed := globalNewMainName structured
      let prepared := globalRenameDecls start renamed (globalResortDecls structured)
      let globals := globalCompileTop bytesInWord fromNat prepared
      let entryArguments := entry.params.map (fun parameter =>
        Exp.var .local parameter.1)
      let wrapper : Decl α := .function
        { name := start
          inline := false
          exported := false
          params := entry.params
          body := .seq (nestedSeq globals.initializers)
            (.call none renamed entryArguments)
          returnShape := entry.returnShape }
      let globals := { globals with declarations := wrapper :: globals.declarations }
      let crepeContext := pipelineCrepeContext bytesInWord fromNat globals
      let compiled := compileToCrep crepeContext globals.declarations
      let crepe := crepSimpFunctions fromNat
        (crepInlineTopRecursiveByNames (pipelineInlineNames globals.declarations) compiled)
      let loop := pipelineLoopFunctionsSource architecture 1 crepe
      let word := pipelineWordFunctions loop
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

/-! Target entry point.  `pan_to_target` first supplies a zero-returning
    `main` when the source has no entry function, then takes the exact entry
    wrapper path.  This matters even when the caller only asks for the
    intermediate pipeline: the synthetic function changes declaration order,
    labels, and the linked artifact. -/
def compileFlapjackTarget [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [AndOp α] [ShiftRight α] [PanShiftWidth α]
    (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    FlapjackPipelineResult α :=
  let declarations := panTargetDeclarationsWithDefaultMain declarations
  match compileFlapjackEntry architecture bytesInWord fromNat "main" declarations with
  | some result => result
  | none => compileFlapjackCore architecture bytesInWord fromNat declarations

/-! Public source compiler entry point.  Cake's `pan_to_target` wrapper is the
    default behavior: global initializers execute once in the synthesized
    entry wrapper, rather than being prepended to the recursive source `main`.
    The old pass-local implementation remains available as
    `compileFlapjackCore` for the empty-program fallback and intermediate
    fixtures that intentionally exercise the unwrapped pass. -/
def compileFlapjack [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [AndOp α] [ShiftRight α] [PanShiftWidth α]
    (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    FlapjackPipelineResult α :=
  compileFlapjackTarget architecture bytesInWord fromNat declarations

/-! Executable port of `pan_to_word$compile_prog`: compose the existing
    Pancake passes, then expose the source-shaped `loop_to_word` result. -/
def compilePanToWord [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [AndOp α] [ShiftRight α] [PanShiftWidth α]
    (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    List (Nat × Nat × WordProg α) :=
  panToWordCompileProg
    (compileFlapjackTarget architecture bytesInWord fromNat declarations).loop

/-! Target-facing variants of the RISC-V stack pipelines.  These variants make
    the exact `pan_to_target` wrapper available without changing their
    established labels or linked-image contracts. -/

def compileFlapjackRiscVViaStackTarget [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsToStack pipeline.word
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

def compileFlapjackRiscVViaAllocatedStackTarget [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpills pipeline.loop
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

def compileFlapjackRiscVViaAllocatedStackWithFullSsaTarget [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpillsAndFullSsa pipeline.loop
  let initialLabel := fullSsaInitialLabLabel functions
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 initialLabel
    (functions.map (fun (label, _, body) => (label, body)))

def compileFlapjackRiscVViaGraphStackWithFullSsaTarget [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithGraphAndFullSsa pipeline.loop
  let initialLabel := fullSsaInitialLabLabel functions
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 initialLabel
    (functions.map (fun (label, _, body) => (label, body)))

def compileFlapjackRiscVViaAllocatedStackWithBitmapsTarget [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (RiscV.WordStackBitmapState × List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let (functions, bitmaps) ←
    pipelineWordFunctionsAllocatedWithSpillsAndBitmaps
      (RiscV.wordStackInitialBitmaps false) pipeline.loop
  let instructions ←
    RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
      removeConfig 0 0
      (functions.map (fun (label, _, body) => (label, body)))
  pure (bitmaps, instructions)

def compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmapsTarget
    [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (RiscV.WordStackBitmapState × List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let (functions, bitmaps) ←
    pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
      (RiscV.wordStackInitialBitmaps false) pipeline.loop
  let initialLabel := fullSsaInitialLabLabel functions
  let instructions ←
    RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
      removeConfig 0 initialLabel
      (functions.map (fun (label, _, body) => (label, body)))
  pure (bitmaps, instructions)

def compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmapsAndSimpleGcTarget
    [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (RiscV.WordStackBitmapState × List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let loop := pipeline.loop
  let (functions, bitmaps) ←
    pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
      (RiscV.wordStackInitialBitmaps false) loop
  let initialLabel := fullSsaInitialLabLabel functions
  let instructions ←
    RiscV.compileStackProgramNatListWithSimpleGcAndStoreConstsToRiscV
      { services := services } removeConfig
      { gcStubLocation := stackGcStubLocation, returnLabel := 0,
        firstFreshLabel := stackFunctionFirstLabel }
      { } stackStoreConstsStubLocation RiscV.CakeRegAlloc.cakeRiscVRegisterCount
        0 initialLabel
      (functions.map (fun (label, _, body) => (label, body)))
  pure (bitmaps, instructions)

/-! Linked target-facing form of the complete full-SSA bitmap/simple-GC
pipeline.  The bitmap table is retained alongside the resolved Lab sections,
so execution and GC correctness clients can use one artifact. -/
def compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmapsAndSimpleGcTargetLinked
    [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (RiscV.WordStackBitmapState ×
      List (Nat × RiscV.Word width × List (RiscV.Instruction width))) := do
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let loop := pipeline.loop
  let (functions, bitmaps) ←
    pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
      (RiscV.wordStackInitialBitmaps false) loop
  let initialLabel := fullSsaInitialLabLabel functions
  let sections ←
    RiscV.compileStackProgramNatListLinkedWithSimpleGcAndStoreConstsToRiscV
      { services := services } removeConfig
      { gcStubLocation := stackGcStubLocation, returnLabel := 0,
        firstFreshLabel := stackFunctionFirstLabel }
      { } stackStoreConstsStubLocation RiscV.CakeRegAlloc.cakeRiscVRegisterCount
        0 initialLabel
      (functions.map (fun (label, _, body) => (label, body)))
  pure (bitmaps, sections)

/-! Exact source-entry form of the complete bitmap/simple-GC linked artifact.
    As with the non-GC entry wrapper below, keep the source lookup and
    initializer wrapper visible by using compileFlapjackEntry before the
    allocator and runtime sections are assembled. -/
def compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmapsAndSimpleGcEntryLinked
    [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig) (start : FunName)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (RiscV.WordStackBitmapState ×
      List (Nat × RiscV.Word width × List (RiscV.Instruction width))) := do
  let pipeline ← compileFlapjackEntry architecture bytesInWord fromNat start declarations
  let loop := pipeline.loop
  let (functions, bitmaps) ←
    pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
      (RiscV.wordStackInitialBitmaps false) loop
  let initialLabel := fullSsaInitialLabLabel functions
  let sections ←
    RiscV.compileStackProgramNatListLinkedWithSimpleGcAndStoreConstsToRiscV
      { services := services } removeConfig
      { gcStubLocation := stackGcStubLocation, returnLabel := 0,
        firstFreshLabel := stackFunctionFirstLabel }
      { } stackStoreConstsStubLocation RiscV.CakeRegAlloc.cakeRiscVRegisterCount
        0 initialLabel
      (functions.map (fun (label, _, body) => (label, body)))
  pure (bitmaps, sections)

def compileFlapjackRiscVViaStack [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsToStack pipeline.word
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

/-! End-to-end RISC-V entry point using the executable Word allocator before
    the Word-to-Stack and StackRemove boundaries.  This is deliberately a
    separate API because the historical entry point above is useful for
    register-coloured fixtures that do not exercise allocation failure. -/
def compileFlapjackRiscVViaAllocatedStack [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpills pipeline.loop
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

/-! End-to-end allocator entry point using the complete CakeML-style SSA
    function program, including ABI formal-parameter moves.  LabLang reserves
    labels 0 and 1 for the public and tail-sequence entries, so full-SSA
    sections start fresh continuation labels at 2. -/
def compileFlapjackRiscVViaAllocatedStackWithFullSsa [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpillsAndFullSsa pipeline.loop
  let initialLabel := fullSsaInitialLabLabel functions
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 initialLabel
    (functions.map (fun (label, _, body) => (label, body)))

/-! End-to-end graph-colouring entry point using the complete CakeML-style SSA
    function program.  This is kept alongside the spill-backed full-SSA
    wrapper so callers can compare the two allocation strategies after the
    shared Word-to-Stack and StackRemove stages. -/
def compileFlapjackRiscVViaGraphStackWithFullSsa [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithGraphAndFullSsa pipeline.loop
  let initialLabel := fullSsaInitialLabLabel functions
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 initialLabel
    (functions.map (fun (label, _, body) => (label, body)))

/-! Bitmap-carrying variant of the allocator-aware RISC-V entry point.  The
    returned bitmap table is part of the artifact because the later runtime
    initialization pass must place it in the bitmap buffer before execution. -/
def compileFlapjackRiscVViaAllocatedStackWithBitmaps [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (RiscV.WordStackBitmapState × List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let (functions, bitmaps) ←
    pipelineWordFunctionsAllocatedWithSpillsAndBitmaps
      (RiscV.wordStackInitialBitmaps false) pipeline.loop
  let instructions ←
    RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
      removeConfig 0 0
      (functions.map (fun (label, _, body) => (label, body)))
  pure (bitmaps, instructions)

/-! Full-SSA bitmap-carrying entry point.  This is the state-threaded sibling
    of `compileFlapjackRiscVViaAllocatedStackWithFullSsa`; it retains the
    generated bitmap table while compiling the complete entry-inclusive
    function program through StackRemove and LabLang. -/

def compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmaps [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (RiscV.WordStackBitmapState × List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let (functions, bitmaps) ←
    pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
      (RiscV.wordStackInitialBitmaps false) pipeline.loop
  let initialLabel := fullSsaInitialLabLabel functions
  let instructions ←
    RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
      removeConfig 0 initialLabel
      (functions.map (fun (label, _, body) => (label, body)))
  pure (bitmaps, instructions)

/- Full-SSA bitmap entry point with the executable CakeML-shaped runtime
   sections linked in. Its section namespace reserves raise, StoreConsts,
   and the collector before function labels, so StoreConsts calls cannot
   alias the first compiled function. -/
def compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmapsAndSimpleGc
    [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (RiscV.WordStackBitmapState × List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let loop := pipelineLoopFunctionsSource architecture stackFunctionFirstLabel pipeline.crepe
  let (functions, bitmaps) ←
    pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmaps
      (RiscV.wordStackInitialBitmaps false) loop
  let initialLabel := fullSsaInitialLabLabel functions
  let instructions ←
    RiscV.compileStackProgramNatListWithSimpleGcAndStoreConstsToRiscV
      { services := services } removeConfig
      { gcStubLocation := stackGcStubLocation, returnLabel := 0,
        firstFreshLabel := stackFunctionFirstLabel }
      { } stackStoreConstsStubLocation RiscV.CakeRegAlloc.cakeRiscVRegisterCount
        0 initialLabel
      (functions.map (fun (label, _, body) => (label, body)))
  pure (bitmaps, instructions)

/-! End-to-end entry point using the graph-coloured allocator.  This keeps the
graph allocator selectable while its complete CakeML spill metadata is still
being filled in. -/
def compileFlapjackRiscVViaGraphAllocatedStack [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (RiscV.Instruction width)) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithGraph pipeline.loop
  RiscV.compileStackProgramNatListWithRaiseStubToRiscV { services := services }
    removeConfig 0 0
    (functions.map (fun (label, _, body) => (label, body)))

/-! Linked graph-allocator artifact.  Keep the section labels and byte entry
    addresses produced by LabLang so callers can choose an exported function
    and establish the machine-state relation at its actual entry point. -/
def compileFlapjackRiscVViaGraphAllocatedStackLinked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (Nat × RiscV.Word width × List (RiscV.Instruction width))) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithGraph pipeline.loop
  RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscV { services := services }
    removeConfig 0 0 (functions.map (fun (label, _, body) => (label, body)))

/-! Linked form of the allocator-aware entry point.  The flat instruction
    stream remains available above; this form additionally records each
    function's byte entry address so an execution harness can select an
    exported function and install its generated sections in memory. -/
def compileFlapjackRiscVViaAllocatedStackLinked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (Nat × RiscV.Word width × List (RiscV.Instruction width))) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpills pipeline.loop
  RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscV { services := services }
    removeConfig 0 0 (functions.map (fun (label, _, body) => (label, body)))

/-! Linked artifact for the complete full-SSA spill path.  The section entry
    addresses are retained so an execution or correctness client can select
    the generated function without reconstructing LabLang layout. -/
def compileFlapjackRiscVViaAllocatedStackWithFullSsaLinked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (Nat × RiscV.Word width × List (RiscV.Instruction width))) := do
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpillsAndFullSsa pipeline.loop
  let initialLabel := fullSsaInitialLabLabel functions
  RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscV { services := services }
    removeConfig 0 initialLabel (functions.map (fun (label, _, body) => (label, body)))

/-! Checked counterpart of the full-SSA linked entry point.  Static checking
is performed before any of the expensive lowering and allocation stages, so
malformed source declarations cannot be mistaken for allocator failure. -/
def compileFlapjackRiscVViaAllocatedStackWithFullSsaLinkedChecked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    StaticResult
      (Option (List (Nat × RiscV.Word width × List (RiscV.Instruction width)))) :=
  staticBind (staticCheck declarations) (fun _ =>
    staticOk (compileFlapjackRiscVViaAllocatedStackWithFullSsaLinked
      architecture bytesInWord fromNat services removeConfig declarations))

/-! Target-facing full-SSA entry point.  `pan_to_target` guarantees that the
program has a leading `main`; retain that convention for the linked,
allocation-aware RISC-V path instead of requiring every caller to synthesize
one first. -/
def compileFlapjackRiscVViaAllocatedStackWithFullSsaTargetLinked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (Nat × RiscV.Word width × List (RiscV.Instruction width))) := do
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpillsAndFullSsa pipeline.loop
  let initialLabel := fullSsaInitialLabLabel functions
  RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscV { services := services }
    removeConfig 0 initialLabel (functions.map (fun (label, _, body) => (label, body)))

def compileFlapjackRiscVViaAllocatedStackWithFullSsaTargetLinkedChecked
    [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig)
    (declarations : List (Decl (RiscV.Word width))) :
    StaticResult
      (Option (List (Nat × RiscV.Word width × List (RiscV.Instruction width)))) :=
  staticBind (staticCheck declarations) (fun _ =>
    staticOk (compileFlapjackRiscVViaAllocatedStackWithFullSsaTargetLinked
      architecture bytesInWord fromNat services removeConfig declarations))

/-! Exact source-entry sibling of the target-facing full-SSA linked pipeline.
    `compileFlapjackEntry` performs the CakeML-style source lookup, renaming,
    initializer wrapper, and reference permutation before the allocator sees
    the program.  Keep the `Option` result visible so a missing requested
    entry is reported instead of silently synthesizing `main`. -/
def compileFlapjackRiscVViaAllocatedStackWithFullSsaEntryLinked [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig) (start : FunName)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (List (Nat × RiscV.Word width × List (RiscV.Instruction width))) := do
  let pipeline ← compileFlapjackEntry architecture bytesInWord fromNat start declarations
  let functions ← pipelineWordFunctionsAllocatedWithSpillsAndFullSsa pipeline.loop
  let initialLabel := fullSsaInitialLabLabel functions
  RiscV.compileStackProgramNatListLinkedWithRaiseStubToRiscVCake { services := services }
    removeConfig 0 initialLabel (functions.map (fun (label, _, body) => (label, body)))

def compileFlapjackChecked [BEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [AndOp α] [ShiftRight α] [PanShiftWidth α]
    (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    StaticResult (FlapjackPipelineResult α) :=
  staticBind (staticCheck declarations) (fun _ =>
    staticOk (compileFlapjack architecture bytesInWord fromNat declarations))

structure FlapjackRiscVResult (width : Nat) [NeZero width] where
  pipeline : FlapjackPipelineResult (RiscV.Word width)
  functions : List (Nat × List Nat ×
    Option (List (RiscV.Instruction width) × List (Fin 32)))
  linkedFunctions : Option (List (Nat × RiscV.Word width × List Nat ×
    List (RiscV.Instruction width) × List (Fin 32)))
  callLinkedFunctions : Option (List (Nat × RiscV.Word width × List Nat ×
    List (RiscV.Instruction width) × List (Fin 32)))

def compileFlapjackRiscV [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width)
    (declarations : List (Decl (RiscV.Word width))) : FlapjackRiscVResult width :=
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions := pipelineRiscVFunctions pipeline.word
  { pipeline := pipeline
    functions := functions
    linkedFunctions := RiscV.linkRiscVFunctions 0 functions
    callLinkedFunctions := RiscV.linkWordFunctions 0 pipeline.word }

/-! RISC-V artifact wrapper for the exact entry-point pipeline.  Its `Option`
    result reflects CakeML's behavior when the requested source entry is not
    present. -/
def compileFlapjackRiscVEntry [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (start : FunName)
    (declarations : List (Decl (RiscV.Word width))) :
    Option (FlapjackRiscVResult width) := do
  let pipeline ← compileFlapjackEntry architecture bytesInWord fromNat start declarations
  let functions := pipelineRiscVFunctions pipeline.word
  pure (FlapjackRiscVResult.mk pipeline functions
    (RiscV.linkRiscVFunctions 0 functions)
    (RiscV.linkWordFunctions 0 pipeline.word))

def compileFlapjackRiscVTarget [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width)
    (declarations : List (Decl (RiscV.Word width))) : FlapjackRiscVResult width :=
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let functions := pipelineRiscVFunctions pipeline.word
  { pipeline := pipeline
    functions := functions
    linkedFunctions := RiscV.linkRiscVFunctions 0 functions
    callLinkedFunctions := RiscV.linkWordFunctions 0 pipeline.word }

def compileFlapjackRiscVWithFfi [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (declarations : List (Decl (RiscV.Word width))) : FlapjackRiscVResult width :=
  let pipeline := compileFlapjackCore architecture bytesInWord fromNat declarations
  let functions := pipelineRiscVFunctionsWithFfi services pipeline.word
  { pipeline := pipeline
    functions := functions
    linkedFunctions := RiscV.linkRiscVFunctions 0 functions
    callLinkedFunctions := RiscV.linkWordFunctionsWithFfi 0 services pipeline.word }

def compileFlapjackRiscVTargetWithFfi [NeZero width]
    [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width) (services : List (FunName × Nat))
    (declarations : List (Decl (RiscV.Word width))) : FlapjackRiscVResult width :=
  let pipeline := compileFlapjackTarget architecture bytesInWord fromNat declarations
  let functions := pipelineRiscVFunctionsWithFfi services pipeline.word
  { pipeline := pipeline
    functions := functions
    linkedFunctions := RiscV.linkRiscVFunctions 0 functions
    callLinkedFunctions := RiscV.linkWordFunctionsWithFfi 0 services pipeline.word }

def compileFlapjackRiscVChecked [NeZero width] [BEq (RiscV.Word width)]
    [OfNat (RiscV.Word width) 0] [OfNat (RiscV.Word width) 1]
    [Add (RiscV.Word width)] [Mul (RiscV.Word width)]
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word width)
    (fromNat : Nat → RiscV.Word width)
    (declarations : List (Decl (RiscV.Word width))) :
    StaticResult (FlapjackRiscVResult width) :=
  staticBind (staticCheck declarations) (fun _ =>
    staticOk (compileFlapjackRiscV architecture bytesInWord fromNat declarations))

theorem compileFlapjack_skip [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [AndOp α] [ShiftRight α] [PanShiftWidth α]
    (architecture : RiscV.Architecture) (bytesInWord : α) (fromNat : Nat → α) :
    (compileFlapjack architecture bytesInWord fromNat []).simplified = [] := by
  simp [compileFlapjack, compileFlapjackTarget, compileFlapjackEntry,
    pipelineFindFunction, panTargetDeclarationsWithDefaultMain,
    panTargetMoveStartToFront, globalDeclsFilter, compileFlapjackCore,
    panSimpDecls, structCompileTop, structGetNames, structCompileDecls,
    globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext, pipelineLoopFunctions,
    pipelineWordFunctions, pipelinePrependInitializers]

end Flapjack
