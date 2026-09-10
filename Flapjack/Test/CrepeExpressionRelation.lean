import Flapjack.CrepeExpressionRelation

namespace Flapjack

/-! Regression for the locality domain used by the source-to-Crep proof. -/

theorem localise_dec_return_is_localised :
    localisedProg
      (Parser.localiseProg []
        (.dec "x" .one (.const (7 : Nat))
          (.return (.var .global "x"))) : Prog Nat) := by
  simp [Parser.localiseProg, Parser.localiseExp, Parser.localiseKind,
    localisedProg, localisedExp, expGlobalVars]

theorem global_assignment_is_outside_correctness_domain :
    ¬ localisedProg (.assign .global "x" (.const (7 : Nat)) : Prog Nat) := by
  simp [localisedProg]

end Flapjack
