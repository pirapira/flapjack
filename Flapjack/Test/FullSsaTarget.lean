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

#guard match fullSsaGeneratedMainLinked with
  | some (_ :: _) => true
  | _ => false

#guard match fullSsaGeneratedMainChecked.1 with
  | .ok (some (_ :: _)) => true
  | _ => false

end Flapjack
