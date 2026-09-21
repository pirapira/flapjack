import Flapjack.PanSimpLocalised

/-!
Focused regressions for the `pan_simp` localisation preservation lemmas: they
are instantiated on concrete `Prog Nat` programs so that both the statements
and the constructor case analysis stay exercised.
-/

namespace Flapjack

/-- The clock-free normal fragment is localised. -/
example : localisedProg (.seq (.skip : Prog Nat) (.annot "tag" "text")) := by
  simp [localisedProg]

/-- `seqAssoc` inserts only `Skip`/`Seq` nodes, so localisation survives. -/
example :
    localisedProg (seqAssoc (.skip : Prog Nat)
      (.seq (.skip : Prog Nat) (.annot "tag" "text"))) :=
  localisedProg_seqAssoc _ _ localisedProg_skip (by simp [localisedProg])

/-- A local assignment is a localised program. -/
example : localisedProg (.assign .local "x" (.const (1 : Nat)) : Prog Nat) := by
  simp only [localisedProg, localisedExp, expGlobalVars.eq_1]

/-- The whole `pan_simp` pass preserves localisation on a concrete program. -/
example :
    localisedProg (panSimpProg
      (.seq (.assign .local "x" (.const (1 : Nat))) (.skip : Prog Nat))) :=
  localisedProg_panSimpProg _
    (by
      simp only [localisedProg, localisedExp, expGlobalVars.eq_1]
      trivial)

/-- Global assignments are rejected by the localisation invariant. -/
example : ¬ localisedProg (.assign .global "g" (.const (1 : Nat)) : Prog Nat) := by
  simp [localisedProg]

#check @localisedProg_smartSeq
#check @localisedProg_seqCallRet
#check @localisedProg_seqAssoc
#check @localisedProg_retToTail
#check @localisedProg_panSimpProg

end Flapjack
