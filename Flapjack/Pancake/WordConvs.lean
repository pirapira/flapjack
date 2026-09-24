import Flapjack.HolRef
import Flapjack.Pancake.WordLang

/-!
# CakeML backend `wordConvs` syntactic conventions

Counterpart of `cakeml/compiler/backend/semantics/wordConvsScript.sml`.  This
module ports the label-preservation relation and `extract_labels` over the
faithful backend `wordLang$prog` model of `Flapjack.Pancake.WordLang`; the
remaining conventions land in follow-up slices.

HOL's `set new_labs SUBSET set old_labs` is represented pointwise as
`∀ label, label ∈ newLabels → label ∈ oldLabels`, which is exactly set
inclusion and needs no `DecidableEq` instance; `ALL_DISTINCT` is `List.Nodup`.
The `num_set` cut-set carriers of `WordLangProg` are modelled by
`FiniteMap Nat Unit`, which fixes `num_set` lookup behaviour;
`extract_labels` never inspects them.
-/

namespace Flapjack

/-- Exact source counterpart of CakeML `wordConvs$labels_rel_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:139-143`): labels may be
forgotten but not invented, and distinctness is preserved. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_def"]
def labelsRel (oldLabels newLabels : List β) : Prop :=
  (oldLabels.Nodup → newLabels.Nodup) ∧
    ∀ label, label ∈ newLabels → label ∈ oldLabels

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_refl"]
theorem labelsRel_refl (labels : List β) : labelsRel labels labels :=
  ⟨fun distinct => distinct, fun _ member => member⟩

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_APPEND"]
theorem labelsRel_append {xs xs₁ ys ys₁ : List β}
    (hxs : labelsRel xs xs₁) (hys : labelsRel ys ys₁) :
    labelsRel (xs ++ ys) (xs₁ ++ ys₁) := by
  obtain ⟨hxsDistinct, hxsSubset⟩ := hxs
  obtain ⟨hysDistinct, hysSubset⟩ := hys
  refine ⟨?_, ?_⟩
  · intro hdistinct
    obtain ⟨hxsNodup, hysNodup, hdisjoint⟩ := List.nodup_append.mp hdistinct
    refine List.nodup_append.mpr ⟨hxsDistinct hxsNodup, hysDistinct hysNodup, ?_⟩
    intro a inXs₁ b inYs₁ equal
    exact hdisjoint a (hxsSubset a inXs₁) b (hysSubset b inYs₁) equal
  · intro label member
    rw [List.mem_append] at member
    rw [List.mem_append]
    rcases member with member | member
    · exact Or.inl (hxsSubset label member)
    · exact Or.inr (hysSubset label member)

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_CONS"]
theorem labelsRel_cons {x x₁ : β} {ys ys₁ : List β}
    (hx : labelsRel [x] [x₁]) (hys : labelsRel ys ys₁) :
    labelsRel (x :: ys) (x₁ :: ys₁) := by
  simpa using labelsRel_append hx hys

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_TRANS"]
theorem labelsRel_trans {xs ys zs : List β}
    (hxy : labelsRel xs ys) (hyz : labelsRel ys zs) : labelsRel xs zs := by
  obtain ⟨hxyDistinct, hxySubset⟩ := hxy
  obtain ⟨hyzDistinct, hyzSubset⟩ := hyz
  exact ⟨fun distinct => hyzDistinct (hxyDistinct distinct),
    fun label member => hxySubset label (hyzSubset label member)⟩

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "PERM_IMP_labels_rel"]
theorem labelsRel_of_perm {xs ys : List β} (hperm : xs.Perm ys) : labelsRel ys xs :=
  ⟨fun distinct => hperm.symm.nodup distinct, fun _ member => hperm.subset member⟩

/-- Exact source counterpart of CakeML `wordConvs$extract_labels_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:440-459`): collect the
handler label pairs a program mentions, descending into `Call` return/handler
bodies, `MustTerminate`, `Seq`, `Loop`, and `If`, and returning no labels for
every other constructor.  The `Call` case keeps HOL's nesting: with no return
metadata there are no labels; otherwise the return-handler labels come first
(followed by the handler-body pair when a handler exists, and the
return-handler's own labels last).

HOL's `wordLang$prog` is indexed by the word width `'a` and carries `'a word`
values, so the faithful statement fixes the value carrier to `BitVec width`
(the width is implicit, matching HOL's universally quantified `'a`). -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "extract_labels_def"]
def extractLabels {width : Nat} : WordLangProg (BitVec width) → List (Nat × Nat)
  | .call returns _ _ handler =>
      match returns, handler with
      | none, _ => []
      | some (_, _, returnHandler, l1, l2), none =>
          [(l1, l2)] ++ extractLabels returnHandler
      | some (_, _, returnHandler, l1, l2), some (_, handlerProg, l1', l2') =>
          [(l1, l2), (l1', l2')] ++ extractLabels returnHandler ++
            extractLabels handlerProg
  | .mustTerminate body => extractLabels body
  | .seq first second => extractLabels first ++ extractLabels second
  | .loop _ body _ => extractLabels body
  | .ite _ _ _ thenBranch elseBranch =>
      extractLabels thenBranch ++ extractLabels elseBranch
  | _ => []

/-- Exact source counterpart of CakeML `wordConvs$distinct_tar_reg_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:267-279`): whether an
instruction's destination differs from the registers it reads.  Every other
instruction is accepted. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "distinct_tar_reg_def"]
def distinctTarReg {width : Nat} : WordLangInst (BitVec width) → Bool
  | .arith (.binop _ r1 _ ri) => match ri with
      | .reg r => decide (r ≠ r1)
      | .imm _ => true
  | .arith (.shift _ r1 _ ri) => match ri with
      | .reg r => decide (r ≠ r1)
      | .imm _ => true
  | .arith (.addCarry r1 _ r3 r4 _) => decide (r1 ≠ r3 ∧ r1 ≠ r4)
  | .arith (.addOverflow r1 _ r3 _) => decide (r1 ≠ r3)
  | .arith (.subOverflow r1 _ r3 _) => decide (r1 ≠ r3)
  | _ => true

/-- Exact source counterpart of CakeML `wordConvs$two_reg_inst_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:284-296`): whether an
instruction is two-register (the destination equals the first source) for the
arithmetic forms that require it.  Every other instruction is accepted. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "two_reg_inst_def"]
def twoRegInst {width : Nat} : WordLangInst (BitVec width) → Bool
  | .arith (.binop _ r1 r2 _) => r1 == r2
  | .arith (.shift _ r1 r2 _) => r1 == r2
  | .arith (.addCarry r1 r2 _ _ _) => r1 == r2
  | .arith (.addOverflow r1 r2 _ _) => r1 == r2
  | .arith (.subOverflow r1 r2 _ _) => r1 == r2
  | _ => true

/-- Exact source counterpart of CakeML `wordConvs$every_inst_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:299-315`): whether a
predicate holds on every `Inst` reachable through the program's structural
positions (`Seq`, `Loop`, `If`, `MustTerminate`, `Call` bodies, and the
synthetic instruction of `OpCurrHeap`).  Note HOL's `Call` nesting: when the
return metadata is `NONE` the result is `T` regardless of the handler. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_inst_def"]
def everyInst {width : Nat} (P : WordLangInst (BitVec width) → Bool) :
    WordLangProg (BitVec width) → Bool
  | .inst instruction => P instruction
  | .seq first second => everyInst P first && everyInst P second
  | .loop _ body _ => everyInst P body
  | .ite _ _ _ thenBranch elseBranch => everyInst P thenBranch && everyInst P elseBranch
  | .opCurrHeap bop r1 r2 => P (.arith (.binop bop r1 r2 (.reg r2)))
  | .mustTerminate body => everyInst P body
  | .call returns _ _ handler =>
      match returns with
      | none => true
      | some (_, _, returnHandler, _, _) =>
          everyInst P returnHandler &&
            match handler with
            | none => true
            | some (_, handlerProg, _, _) => everyInst P handlerProg
  | _ => true

/-- HOL `wordConvs$flat_exp_conventions` (`wordConvsScript.sml:179-205`):
whether a program keeps all expressions flat.  Top-level expressions are
forbidden in `Assign` and `Store`, allowed only as `Var` in `Set`, and in
`ShareInst` allowed only as `Var` or `Op Add [Var r; Const c]`.  Descends
through `Seq`, `Loop`, `If`, `MustTerminate` and both `Call` bodies (the
return and handler cases are both required, so a `Call` with no return
metadata but a non-flat handler is rejected). -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "flat_exp_conventions_def"]
def flatExpConventions {width : Nat} : WordLangProg (BitVec width) → Bool
  | .assign _ _ => false
  | .store _ _ => false
  | .set _ (.var _) => true
  | .set _ _ => false
  | .shareInst _ _ (.var _) => true
  | .shareInst _ _ (.op .add [.var _, .const _]) => true
  | .shareInst _ _ _ => false
  | .seq first second => flatExpConventions first && flatExpConventions second
  | .loop _ body _ => flatExpConventions body
  | .ite _ _ _ thenBranch elseBranch =>
      flatExpConventions thenBranch && flatExpConventions elseBranch
  | .mustTerminate body => flatExpConventions body
  | .call returns _ _ handler =>
      (match returns with
        | none => true
        | some (_, _, returnHandler, _, _) => flatExpConventions returnHandler) &&
        (match handler with
          | none => true
          | some (_, handlerProg, _, _) => flatExpConventions handlerProg)
  | _ => true

end Flapjack