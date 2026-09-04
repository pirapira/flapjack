import Flapjack.PanGlobals
import Flapjack.Compile
import Flapjack.CrepToLoop
import Flapjack.Word

/-!
An executable composition of the currently ported Pancake passes.

The result keeps each intermediate representation visible so the eventual
simulation theorem can be proved pass by pass. This composition covers the
front-end normalization and structure/global passes, Pancake-to-Crepe,
Crepe-to-Loop, and Loop-to-Word. Target instruction selection remains partial
and is intentionally separate in `Flapjack.RiscV.Backend`.
-/

namespace Flapjack

def pipelineExceptionCodes (fromNat : Nat → α) : Nat → List (Decl α) → InfoMap α
  | _, [] => []
  | index, .exnDecl exception _ :: declarations =>
      (exception, fromNat index) :: pipelineExceptionCodes fromNat (index + 1) declarations
  | index, _ :: declarations => pipelineExceptionCodes fromNat (index + 1) declarations

def pipelineCrepeContext [BEq α] [Add α]
    (bytesInWord : α) (fromNat : Nat → α)
    (program : GlobalCompiledProgram α) : CompileContext α :=
  { vars := []
    functions := []
    exceptions := pipelineExceptionCodes fromNat 0 program.declarations
    maxVar := 0
    bytesInWord := bytesInWord }

def pipelineFunctionInfos (firstLabel : Nat) :
    List (CompiledFunction α) → InfoMap (Nat × Nat)
  | [] => []
  | function :: functions =>
      (function.name, (firstLabel, function.params.length)) ::
        pipelineFunctionInfos (firstLabel + 1) functions

def pipelineLoopFunctionsAux [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (functionInfos : InfoMap (Nat × Nat)) :
    Nat → List (CompiledFunction α) → List (Nat × List Nat × LoopProg α)
  | _, [] => []
  | label, function :: functions =>
      let context : LoopContext α :=
        { vars := []
          functions := functionInfos
          maxVar := function.params.length
          target := architecture }
      (label, function.params, loopCompileProg context [] function.body) ::
        pipelineLoopFunctionsAux architecture functionInfos (label + 1) functions

def pipelineLoopFunctions [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (firstLabel : Nat)
    (functions : List (CompiledFunction α)) :
    List (Nat × List Nat × LoopProg α) :=
  pipelineLoopFunctionsAux architecture (pipelineFunctionInfos firstLabel functions)
    firstLabel functions

def pipelineWordFunctions [OfNat α 1]
    (functions : List (Nat × List Nat × LoopProg α)) :
    List (Nat × List Nat × WordProg α) :=
  functions.map (fun (label, parameters, body) =>
    (label, parameters, loopToWordProg { vars := [] } body))

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

def compileFlapjack [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    (architecture : RiscV.Architecture) (bytesInWord : α)
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    FlapjackPipelineResult α :=
  let simplified := panSimpDecls declarations
  let structured := structCompileTop simplified
  let globals := globalCompileTop bytesInWord fromNat structured
  let crepeContext := pipelineCrepeContext bytesInWord fromNat globals
  let declarations := pipelinePrependInitializers globals.initializers globals.declarations
  let crepe := compileToCrepe crepeContext declarations
  let loop := pipelineLoopFunctions architecture 1 crepe
  let word := pipelineWordFunctions loop
  { simplified := simplified
    structured := structured
    globals := globals
    crepe := crepe
    loop := loop
    word := word }

theorem compileFlapjack_skip [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    (architecture : RiscV.Architecture) (bytesInWord : α) (fromNat : Nat → α) :
    (compileFlapjack architecture bytesInWord fromNat []).simplified = [] := by
  simp [compileFlapjack, panSimpDecls, structCompileTop, structGetNames,
    structCompileDecls, globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext, pipelineFunctionInfos,
    pipelineLoopFunctions, pipelineWordFunctions, pipelinePrependInitializers]

end Flapjack
