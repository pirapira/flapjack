import Flapjack.Pancake.WordLang
import Flapjack.Pancake.WordConvs

/-! # `every_name` / `every_var` / `every_stack_var` oracle parity

Direct Lean checks against the HOL oracle
`scripts/hol-probes/word_lang_every_name_probe.out`.

`every_name`, `every_var` and `every_stack_var` are Prop-valued here (HOL's are
Bool-valued) and their `num_set` sub-terms use the audited order-insensitive
domain form `everyNumSetKey` because `WordLangNumSet` is a function carrier with
no key enumeration (see `docs/NUM-SET-AUDIT.md`).  They are deliberately NOT
`@[hol]`-tagged.  The `num_set` rows are discharged through
`numSetDomainList`/`everyNumSetKey_iff_list`, showing that HOL's `toAList`
enumeration and our domain form agree. -/

namespace Flapjack.Test.WordLangEveryNameParity

open Flapjack

private abbrev W := BitVec 8

private def pEven : Nat → Bool := fun n => n % 2 = 0
private def pOdd : Nat → Bool := fun n => n % 2 = 1

private def nsEven : WordLangNumSet :=
  fun k => if k = 0 ∨ k = 2 then some () else none
private def nsMixed : WordLangNumSet :=
  fun k => if k = 0 ∨ k = 1 ∨ k = 2 then some () else none
private def emptyCut : WordLangCutsets := ((fun _ => none), (fun _ => none))
private def cutEven : WordLangCutsets := (nsEven, nsEven)
private def cutMixed : WordLangCutsets := (nsMixed, nsEven)

private theorem nsEven_domain : numSetDomainList [0, 2] nsEven := by
  refine ⟨by decide, ?_⟩
  intro k
  by_cases h : k = 0 ∨ k = 2 <;> simp [nsEven, h, List.mem_cons]

private theorem nsMixed_domain : numSetDomainList [0, 1, 2] nsMixed := by
  refine ⟨by decide, ?_⟩
  intro k
  by_cases h : k = 0 ∨ k = 1 ∨ k = 2 <;>
    simp [nsMixed, h, List.mem_cons]

private theorem everyName_even_cutEven : everyName pEven cutEven :=
  ⟨(everyNumSetKey_iff_list nsEven_domain).2 (by decide),
   (everyNumSetKey_iff_list nsEven_domain).2 (by decide)⟩

private theorem not_everyName_even_cutMixed : ¬ everyName pEven cutMixed := by
  intro h
  have h2 := (everyNumSetKey_iff_list nsMixed_domain).1 h.1
  simp [pEven] at h2

private theorem not_everyName_odd_cutMixed : ¬ everyName pOdd cutMixed := by
  intro h
  have h2 := (everyNumSetKey_iff_list nsMixed_domain).1 h.1
  simp [pOdd] at h2

-- every_name rows -----------------------------------------------------------

example : everyName pEven emptyCut :=
  ⟨fun k hk => by simp [emptyCut] at hk,
   fun k hk => by simp [emptyCut] at hk⟩

example : everyName pEven cutEven := everyName_even_cutEven

example : ¬ everyName pEven cutMixed := not_everyName_even_cutMixed

example : everyName pOdd emptyCut :=
  ⟨fun k hk => by simp [emptyCut] at hk,
   fun k hk => by simp [emptyCut] at hk⟩

-- every_var rows ------------------------------------------------------------

private def skipProg : WordLangProg W := .skip
private def assignOk : WordLangProg W := .assign 2 (.const 0)
private def assignBad : WordLangProg W := .assign 3 (.const 0)
private def moveOk : WordLangProg W := .move 0 [(2, 4)]
private def moveBad : WordLangProg W := .move 0 [(2, 3)]

example : everyVar pEven assignOk := by
  simp [everyVar, everyVarExp, pEven, assignOk]
example : ¬ everyVar pEven assignBad := by
  simp [everyVar, everyVarExp, pEven, assignBad]
example : everyVar pEven moveOk := by
  simp [everyVar, pEven, moveOk]
example : ¬ everyVar pEven moveBad := by
  simp [everyVar, pEven, moveBad]
example : everyVar pOdd skipProg := by simp [everyVar, skipProg]
example : ¬ everyVar pEven (.seq assignOk assignBad) := by
  simp [everyVar, everyVarExp, pEven, assignOk, assignBad]
private def callNoneProg : WordLangProg W := .call none none [2] none

example : everyVar pEven callNoneProg := by
  simp [everyVar, pEven, callNoneProg]
private def allocEvenProg : WordLangProg W := .alloc 2 cutEven
private def allocMixedProg : WordLangProg W := .alloc 2 cutMixed

example : everyVar pEven allocEvenProg := by
  refine ⟨by decide, everyName_even_cutEven⟩
example : ¬ everyVar pEven allocMixedProg := by
  intro h
  exact not_everyName_even_cutMixed h.2

-- every_stack_var rows ------------------------------------------------------

example : everyStackVar pEven allocEvenProg := everyName_even_cutEven
example : ¬ everyStackVar pEven allocMixedProg := not_everyName_even_cutMixed
private def callNoneStackProg : WordLangProg W := .call none none [] none

example : everyStackVar pOdd callNoneStackProg := by
  simp [everyStackVar, callNoneStackProg]
private def ffiOkProg : WordLangProg W := .ffi "" 2 4 6 8 cutEven
private def ffiOddRegProg : WordLangProg W := .ffi "" 2 4 6 9 cutEven

example : everyStackVar pEven ffiOkProg := everyName_even_cutEven
example : everyStackVar pEven ffiOddRegProg := everyName_even_cutEven
private def seqMixedBadProg : WordLangProg W := .seq skipProg allocMixedProg

example : ¬ everyStackVar pOdd seqMixedBadProg := by
  intro h
  exact not_everyName_odd_cutMixed h.2

def runChecks : IO Bool := do
  IO.println "PASS wordLang every_name/every_var/every_stack_var match all 19 oracle rows"
  pure true

end Flapjack.Test.WordLangEveryNameParity
