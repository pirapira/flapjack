import Flapjack.Basis.Pure.MlString

namespace Flapjack.Test.MlStringParity

open Flapjack.Basis.Pure.MlString

/-- Character codes used by the oracle rows (`CHR n`). -/
private def c (n : Nat) : HolChar := BitVec.ofNat 8 n

/-- Lean reproduction of the HOL `strlen`/`LENGTH (explode ...)` observation. -/
private def strlen (s : MlString) : Nat := s.explode.length

/-- Reproduces the eight direct HOL-EVAL rows of
    `scripts/hol-probes/mlstring_carrier_probe.out` (bead
    `flapjack-pxn.18.5.15.3.11.2.1`). -/
private def parityGuard : Bool :=
  (strlen (MlString.implode [c 65, c 66, c 67]) == 3) &&
  ((c 0).toNat == 0) &&
  ((c 255).toNat == 255) &&
  ((c (c 200).toNat) == c 200) &&
  ((MlString.implode [c 65, c 66]).explode.length == 2) &&
  (MlString.implode ((MlString.implode [c 65, c 66]).explode) ==
    MlString.implode [c 65, c 66]) &&
  ((MlString.implode [c 65, c 66]).explode == [c 65, c 66]) &&
  (([MlString.implode [c 65], MlString.implode [c 66, c 67]].map
      MlString.explode).flatten.length == 3)

#eval parityGuard
#guard parityGuard

example : (MlString.implode [c 65, c 66]).explode = [c 65, c 66] := rfl

example (s : MlString) : MlString.implode s.explode = s := MlString.implode_explode s

end Flapjack.Test.MlStringParity