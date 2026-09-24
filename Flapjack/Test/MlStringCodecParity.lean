import Flapjack.Compiler.Backend.MlString

/-! Regression for the untagged Lean `String` <-> exact `mlstring` byte codec in
`Flapjack/Compiler/Backend/MlString.lean` (bead `flapjack-pxn.18.5.15.3.11.2.3`).
-/

namespace Flapjack.Test.MlStringCodecParity

open Flapjack.Compiler.Backend.MlString

private def b (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

private def codecGuard : Bool :=
  (ofString "ABC" == MlString.implode [b 65, b 66, b 67]) &&
  (toStringOfBytes (MlString.implode [b 65, b 66, b 67]) == "ABC") &&
  (ofString (toStringOfBytes (MlString.implode [b 0, b 255])) ==
    MlString.implode [b 0, b 255]) &&
  (toStringOfBytes (ofString "AB") == "AB")

#eval codecGuard
#guard codecGuard

example : ofString "ABC" = MlString.implode [b 65, b 66, b 67] := rfl

example : toStringOfBytes (MlString.implode [b 65, b 66, b 67]) = "ABC" := by decide

example (m : MlString) : ofString (toStringOfBytes m) = m := ofString_toStringOfBytes m

example : toStringOfBytes (ofString "AB") = "AB" := rfl

def runChecks : IO Bool := do
  IO.println "PASS Lean String <-> exact mlstring byte codec round trips"
  pure codecGuard

end Flapjack.Test.MlStringCodecParity
