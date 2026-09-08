import Flapjack.Test.FullSsaPipeline

namespace Flapjack

def fullSsaGeneratedMainLinked :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaTargetLinked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
    fullSsaPipelineRemoveConfig []

def fullSsaGeneratedMainChecked :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaTargetLinkedChecked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
    fullSsaPipelineRemoveConfig []

def fullSsaGeneratedMainLookupEntry (label : Nat) :
    List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64)) →
      Option (RiscV.Word 64)
  | [] => none
  | (candidate, entry, _) :: sections =>
      if candidate == label then some entry
      else fullSsaGeneratedMainLookupEntry label sections

def fullSsaGeneratedMainMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← fullSsaGeneratedMainLinked
  let entry ← fullSsaGeneratedMainLookupEntry 1 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAt 100 0 entry 88 [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 88)

def fullSsaGeneratedMainSource : Prog (RiscV.Word 64) :=
  .return (.const (BitVec.ofNat 64 0))

#guard match fullSsaGeneratedMainLinked with
  | some (_ :: _) => true
  | _ => false

#guard match fullSsaGeneratedMainChecked.1 with
  | .ok (some (_ :: _)) => true
  | _ => false

#guard fullSsaGeneratedMainMachineResult = some [BitVec.ofNat 64 0]

#guard
  (evalPanProgWithCallsAndFfi [] (fun _ _ _ _ _ locals => some locals) 10
    (fun _ => none) fullSsaGeneratedMainSource).map (fun result =>
      match result with
      | .returned _ values => values
      | _ => []) = some [BitVec.ofNat 64 0]

end Flapjack
