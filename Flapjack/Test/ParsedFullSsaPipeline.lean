import Flapjack.Test.FullSsaPipeline
import Flapjack.Parser
import Flapjack.Static

namespace Flapjack

open RiscV

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
      fullSsaPipelineRemoveConfig "main" declarations)

def parsedCallLookupEntry (label : Nat) :
    List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64)) →
      Option (RiscV.Word 64)
  | [] => none
  | (candidate, entry, _) :: sections =>
      if candidate == label then some entry
      else parsedCallLookupEntry label sections

def parsedCallMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← parsedCallLinked
  let entry ← parsedCallLookupEntry 2 sections
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
  let (_, body) ← lookupLoopFunction 1 pipeline.loop
  let result ← evalLoopProgWithFunctions pipeline.loop 100
    identityCallLoopState body
  pure (loopResultValues result)

#guard parsedCallDeclarations.isSome
#guard parsedCallLinked.isSome
#guard parsedCallMachineResult = some [BitVec.ofNat 64 41]
#guard parsedCallSourceResult = some [BitVec.ofNat 64 41]
#guard parsedCallLoopResult = some [BitVec.ofNat 64 41]

theorem parsedCall_source_machine_agreement :
    parsedCallSourceResult = parsedCallMachineResult := by
  decide +kernel

theorem parsedCall_source_loop_agreement :
    parsedCallSourceResult = parsedCallLoopResult := by
  decide +kernel

end Flapjack
