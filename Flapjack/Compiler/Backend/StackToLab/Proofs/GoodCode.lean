import Flapjack.Compiler.Backend.StackProps.AllocArg
import Flapjack.Compiler.Backend.StackProps.RegisterBounds
import Flapjack.Compiler.Backend.StackProps.CallArgs
import Flapjack.Compiler.Backend.StackProps.OrderedLabels
import Flapjack.Compiler.Backend.BackendCommon

/-! `good_code_def` and `contain_def` (`stack_to_labProofScript.sml:3349-3363`):
the syntactic conditions on the input procedures of `full_make_init_semantics`,
and its `Abbrev` wrapper. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.GoodCode
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- HOL `good_code_def`. `EVERY` over a list is a membership quantifier, the
tuple lambdas are rendered by projections, and `ALL_DISTINCT` is `List.Nodup`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "good_code_def"
  (words_as_type_indexed_bitvec)]
def goodCode {width : Nat} [NeZero width] (sp : Nat) (code : List (Nat × HolProg width)) :
    Prop :=
  (code.map Prod.fst).Nodup ∧
  (∀ kp ∈ code, stackNumStubs ≤ kp.1 ∧ StackProps.allocArg kp.2) ∧
  (∀ p ∈ code.map Prod.snd, StackProps.callArgs p 1 2 3 4 0) ∧
  (∀ p ∈ code.map Prod.snd, StackProps.regBound p sp) ∧
  (∀ np ∈ code,
    (∀ l ∈ StackPropsCodeLabels.extractLabels np.2, l.1 = np.1 ∧ l.2 ≠ 0 ∧ l.2 ≠ 1) ∧
    (StackPropsCodeLabels.extractLabels np.2).Nodup)

/-- HOL `contain_def`: `contain b = Abbrev b`, where `markerTheory.Abbrev` is
the identity marker (`Abbrev x = x`). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "contain_def"]
def contain (b : Prop) : Prop := b

end Flapjack.Compiler.Backend.StackToLab.Proofs.GoodCode
