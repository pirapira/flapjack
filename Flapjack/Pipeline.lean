import Flapjack.PanGlobals
import Flapjack.Compile
import Flapjack.CrepToLoop
import Flapjack.Word
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Loops
import Flapjack.RiscV.Link

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
    let slots := loopAccVars body parameters
    let context : WordContext :=
      { vars := slots.map (fun name => (name, name + 2)) }
    (label, parameters.map (fun name => name + 2), loopToWordProg context body))

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

def compileFlapjackChecked [BEq String] [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] (architecture : RiscV.Architecture) (bytesInWord : α)
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
  let pipeline := compileFlapjack architecture bytesInWord fromNat declarations
  let functions := pipelineRiscVFunctions pipeline.word
  { pipeline := pipeline
    functions := functions
    linkedFunctions := RiscV.linkRiscVFunctions 0 functions
    callLinkedFunctions := RiscV.linkWordFunctions 0 pipeline.word }

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
    (architecture : RiscV.Architecture) (bytesInWord : α) (fromNat : Nat → α) :
    (compileFlapjack architecture bytesInWord fromNat []).simplified = [] := by
  simp [compileFlapjack, panSimpDecls, structCompileTop, structGetNames,
    structCompileDecls, globalCompileTop, globalCollect, globalCompileDecls,
    globalCompileInitializers, pipelineCrepeContext, pipelineFunctionInfos,
    pipelineLoopFunctions, pipelineWordFunctions, pipelinePrependInitializers]

end Flapjack
