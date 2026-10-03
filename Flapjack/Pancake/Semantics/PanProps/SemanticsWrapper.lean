import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Misc.LprefixLub
import Flapjack.FfiHOL

namespace Flapjack

open Classical in
/-- Original generic PanProps wrapper over arbitrary clock-indexed results.
The PanProps result datatype is distinct from the identically shaped
CrepToLoop result datatype. No event-chain or supplied-LUB premise is needed:
the reviewed chain-free HolLList operation implements the original LUB formula.
HOL SOME-choice is rendered by holOptionSome/Classical.choose; as for the
reviewed carrier, no cross-language agreement of unspecified selections is
claimed. On prefix-chain families the LUB has its usual unique characterization.
This observation definition is noncomputable, just as the original HOL choice
formula; executed compiler routing is a separate obligation. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "semantics_wrapper_def"]
noncomputable def panPropsSemanticsWrapper
    (f : Nat → SemanticsRunResHOL HolOutcome × List HolIoEvent) : HolBehaviour :=
  if ∃ k v, f k = (.RunError, v) then .fail
  else
    match holOptionSome (fun res => ∃ k r ev,
        f k = (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub
        (fun l => ∃ k, l = HolLList.fromList (f k).2))

end Flapjack
