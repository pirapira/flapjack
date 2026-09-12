import Flapjack.Pipeline
import Flapjack.Parser
import Flapjack.Static
import Flapjack.Semantics
import Flapjack.LoopSemantics

namespace Flapjack

open RiscV

def parsedCallPipelineRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def parsedCallLoopState : LoopState (RiscV.Word 64) :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

/-! A source-facing execution regression.  The declarations are obtained from
    the Pancake parser rather than assembled directly as Lean AST values. -/

def parsedCallSource : String :=
  "fun 1 id(1 x) { return x; }\nfun 1 main() { var 1 answer = id(41); return answer; }"

def parsedCallDeclarations : Option (List (Decl (RiscV.Word 64))) :=
  (Parser.parseTopDecs (BitVec.ofInt 64) parsedCallSource).toOption

def parsedCallSourceFunctions :
    Option (List (FunName × List VarName × Prog (RiscV.Word 64))) :=
  parsedCallDeclarations.map (fun declarations =>
    declarations.filterMap (fun declaration =>
      match declaration with
      | .function function =>
          some (function.name, function.params.map Prod.fst, function.body)
      | _ => none))

def parsedCallSourceMain : Option (Prog (RiscV.Word 64)) :=
  parsedCallDeclarations.bind (fun declarations =>
    declarations.findSome? (fun declaration =>
      match declaration with
      | .function function =>
          if function.name == "main" then some function.body else none
      | _ => none))

def parsedCallLinked :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  parsedCallDeclarations.bind (fun declarations =>
    compileFlapjackRiscVViaAllocatedStackWithFullSsaEntryLinked .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      parsedCallPipelineRemoveConfig "main" declarations)

def parsedCallLookupEntry (label : Nat) :
    List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64)) →
      Option (RiscV.Word 64)
  | [] => none
  | (candidate, entry, _) :: sections =>
      if candidate == label then some entry
      else parsedCallLookupEntry label sections

def parsedCallMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← parsedCallLinked
  let entry ← parsedCallLookupEntry 3 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAtAfterEntry 4000 0 entry 172 [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 6)

def parsedCallSourceResult : Option (List (RiscV.Word 64)) := do
  let functions ← parsedCallSourceFunctions
  let body ← parsedCallSourceMain
  let result ← evalPanProgWithCalls functions 30 (fun _ => none) body
  pure result.2

def parsedCallLoopResult : Option (List (RiscV.Word 64)) := do
  let declarations ← parsedCallDeclarations
  let pipeline ← compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
    (fun value => BitVec.ofNat 64 value) "main" declarations
  let (_, body) ← lookupLoopFunction 3 pipeline.loop
  let result ← evalLoopProgWithFunctions pipeline.loop 100
    parsedCallLoopState body
  pure (loopResultValues result)

def parsedCallWordResult : Option (List (RiscV.Word 64)) := do
  let declarations ← parsedCallDeclarations
  let pipeline ← compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
    (fun value => BitVec.ofNat 64 value) "main" declarations
  let (_, body) ← RiscV.lookupWordFunction 3 pipeline.word
  let result ← RiscV.evalWordFunctionWithCalls pipeline.word 100
    (RiscV.zeroState 64) body
  pure result.2

#guard parsedCallDeclarations.isSome

/-! Keep the expensive parser/pipeline reduction in one native executable
    decision.  Repeating it in separate `#guard`s made every fresh CI build
    re-elaborate the full compiler several times. -/

theorem parsedCall_all_agreement :
    parsedCallSourceResult = parsedCallMachineResult ∧
    parsedCallSourceResult = parsedCallLoopResult ∧
    parsedCallSourceResult = parsedCallWordResult := by
  native_decide


theorem parsedCall_source_machine_agreement :
    parsedCallSourceResult = parsedCallMachineResult := by
  exact parsedCall_all_agreement.1

theorem parsedCall_source_loop_agreement :
    parsedCallSourceResult = parsedCallLoopResult := by
  exact parsedCall_all_agreement.2.1

theorem parsedCall_source_word_agreement :
    parsedCallSourceResult = parsedCallWordResult := by
  exact parsedCall_all_agreement.2.2

end Flapjack
