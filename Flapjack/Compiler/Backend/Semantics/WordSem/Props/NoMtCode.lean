import Flapjack.Pancake.WordConvs.NotCreated
import Flapjack.Misc.Sptree
namespace Flapjack
namespace WordProps

/-- HOL `no_mt_code_def` (`wordPropsScript.sml:4772-4775`): no code entry
contains `MustTerminate`. The word dimension is the only representation
translation; the tree carrier and lookup are the reviewed HOL
constructor-for-constructor port. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml"
  "no_mt_code_def" (words_as_type_indexed_bitvec)]
def noMtCode {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ (k n : Nat) (p : WordLangProgHOL (BitVec width)),
    sptLookup k code = some (n, p) → noMtSubprogsHOL p = true
end WordProps
end Flapjack
