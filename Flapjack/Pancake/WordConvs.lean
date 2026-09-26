import Flapjack.HolRef
import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Compiler.Backend.RegAlloc

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

open Flapjack.Compiler.Encoders.Asm

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

HOL's `wordLang$prog` carries `num_set` and `mlstring` fields exactly in the
WordLangProgHOL carrier below. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "extract_labels_def"]
def extractLabels {width : Nat} : WordLangProgHOL (BitVec width) → List (Nat × Nat)
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
instruction is accepted.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def distinctTarReg {width : Nat} : WordLangInst (BitVec width) → Bool
  | .arith (.binop _ r1 _ ri) => match ri with
      | .reg r => decide (r ≠ r1)
      | .imm _ => true
  | .arith (.shift _ r1 _ ri) => match ri with
      | .reg r => decide (r ≠ r1)
      | .imm _ => true
  | .arith (.addCarry r1 _ r3 r4) => decide (r1 ≠ r3 ∧ r1 ≠ r4)
  | .arith (.addOverflow r1 _ r3 _) => decide (r1 ≠ r3)
  | .arith (.subOverflow r1 _ r3 _) => decide (r1 ≠ r3)
  | _ => true

/-- Exact source counterpart of CakeML `wordConvs$two_reg_inst_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:284-296`): whether an
instruction is two-register (the destination equals the first source) for the
arithmetic forms that require it.  Every other instruction is accepted.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def twoRegInst {width : Nat} : WordLangInst (BitVec width) → Bool
  | .arith (.binop _ r1 r2 _) => r1 == r2
  | .arith (.shift _ r1 r2 _) => r1 == r2
  | .arith (.addCarry r1 r2 _ _) => r1 == r2
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
    WordLangProgHOL (BitVec width) → Bool
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
def flatExpConventions {width : Nat} : WordLangProgHOL (BitVec width) → Bool
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

/-- Exact source counterpart of CakeML `wordConvs$inst_ok_less_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:208-249`).  This is the
weaker per-instruction well-formedness predicate used by
`compile_to_word_conventions2`: unlike `asm$inst_ok` it omits the operand
register checks and only constrains the configuration-dependent immediate and
offset conditions.  The `Mem` branch lists `Load`/`Store`/`Load16`/`Store16`/
`Load32`/`Store32` in its first case, so the `hw_offset_ok` case is only
reachable for the remaining memops in the HOL definition.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def instOkLess {width : Nat} (config : AsmConfig width) :
    WordLangInst (BitVec width) → Bool
  | .arith (.binop operator _ _ (.imm value)) => config.validImm (.inl operator) value
  | .arith (.shift operator _ _ (.imm value)) =>
      (!(value == 0) || operator == .lsl) && value.toNat < width
  | .arith (.div ..) =>
      config.isa == .armv8 || config.isa == .mips || config.isa == .riscv
  | .arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) =>
      (!(config.isa == .armv7) || !(destinationLeft == destinationRight)) &&
        (!(config.isa == .armv8 || config.isa == .riscv || config.isa == .ag32) ||
          (!(destinationLeft == sourceLeft) && !(destinationLeft == sourceRight)))
  | .arith (.longDiv ..) => config.isa == .x86_64
  | .arith (.addCarry destination _ sourceLeft sourceRight) =>
      (!(config.isa == .mips || config.isa == .riscv) ||
        (!(destination == sourceLeft) && !(destination == sourceRight)))
  | .arith (.addOverflow destination _ sourceLeft _) =>
      (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))
  | .arith (.subOverflow destination _ sourceLeft _) =>
      (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))
  | .mem operator _ (.addr _ offset) =>
      (if operator == .load || operator == .store || operator == .load16 ||
          operator == .store16 || operator == .load32 || operator == .store32 then
        asmAddrOffsetOk config offset
       else if operator == .load16 || operator == .store16 then
        asmHwOffsetOk config offset
       else
        asmByteOffsetOk config offset)
  | .fp (.fpLess _ left right) => asmFpRegOk config left && asmFpRegOk config right
  | .fp (.fpLessEqual _ left right) => asmFpRegOk config left && asmFpRegOk config right
  | .fp (.fpEqual _ left right) => asmFpRegOk config left && asmFpRegOk config right
  | .fp (.fpAbs destination source) =>
      (!config.twoRegArith || !(destination == source)) &&
        asmFpRegOk config destination && asmFpRegOk config source
  | .fp (.fpNeg destination source) =>
      (!config.twoRegArith || !(destination == source)) &&
        asmFpRegOk config destination && asmFpRegOk config source
  | .fp (.fpSqrt destination source) =>
      asmFpRegOk config destination && asmFpRegOk config source
  | .fp (.fpAdd destination left right) =>
      (!config.twoRegArith || destination == left) && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fp (.fpSub destination left right) =>
      (!config.twoRegArith || destination == left) && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fp (.fpMul destination left right) =>
      (!config.twoRegArith || destination == left) && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fp (.fpDiv destination left right) =>
      (!config.twoRegArith || destination == left) && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fp (.fpFma destination left right) =>
      (config.isa == .armv7) && 2 < config.fpRegCount && asmFpRegOk config destination &&
        asmFpRegOk config left && asmFpRegOk config right
  | .fp (.fpMov destination source) =>
      asmFpRegOk config destination && asmFpRegOk config source
  | .fp (.fpMovToReg destinationInteger second fpRegister) =>
      (!(width == 32) || !(destinationInteger == second)) && asmFpRegOk config fpRegister
  | .fp (.fpMovFromReg fpRegister destinationInteger second) =>
      (!(width == 32) || !(destinationInteger == second)) && asmFpRegOk config fpRegister
  | .fp (.fpToInt destination source) =>
      asmFpRegOk config destination && asmFpRegOk config source
  | .fp (.fpFromInt destination source) =>
      asmFpRegOk config destination && asmFpRegOk config source
  | _ => true

/-- HOL `wordConvs$full_inst_ok_less_def` (`wordConvsScript.sml:318-345`): the
weaker per-instruction validity predicate lifted over the program, with the
`ShareInst` address-expression restriction via `expToAddr`. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "full_inst_ok_less_def"]
def fullInstOkLess {width : Nat} (config : AsmConfig width) :
    WordLangProgHOL (BitVec width) → Bool
  | .inst value => instOkLess config value
  | .seq first second =>
      fullInstOkLess config first && fullInstOkLess config second
  | .loop _ body _ => fullInstOkLess config body
  | .ite _ _ _ thenBranch elseBranch =>
      fullInstOkLess config thenBranch && fullInstOkLess config elseBranch
  | .mustTerminate body => fullInstOkLess config body
  | .call returns _ _ handler =>
      match returns with
      | none => true
      | some (_, _, returnHandler, _, _) =>
          fullInstOkLess config returnHandler &&
            match handler with
            | none => true
            | some (_, handlerProg, _, _) => fullInstOkLess config handlerProg
  | .shareInst operator _ address =>
      match expToAddrHOL address with
      | some (.addr _ offset) =>
          if operator == .load || operator == .store ||
              operator == .load32 || operator == .store32 then
            asmAddrOffsetOk config offset
          else if operator == .load16 || operator == .store16 then
            asmHwOffsetOk config offset
          else asmByteOffsetOk config offset
      | none => false
  | _ => true

/-- HOL `wordConvs$inst_arg_convention` (`wordConvsScript.sml:378-386`):
per-instruction calling-convention argument placement.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def instArgConvention {width : Nat} : WordLangInst (BitVec width) -> Bool
  | .arith (.addCarry _ _ _ r4) => r4 == 0
  | .arith (.shift _ _ _ (.reg r)) => r == 8
  | .arith (.addOverflow _ _ _ r4) => r4 == 0
  | .arith (.subOverflow _ _ _ r4) => r4 == 0
  | .arith (.longMul r1 r2 r3 r4) =>
      r1 == 6 && r2 == 0 && r3 == 0 && r4 == 4
  | .arith (.longDiv r1 r2 r3 r4 _) =>
      r1 == 0 && r2 == 6 && r3 == 6 && r4 == 0
  | _ => true

/-- Production helper corresponding to HOL `call_arg_convention_def`.
Untagged because its whole-program argument uses the production AST fields
`FiniteMap Nat Unit` and `String`, rather than HOL's `unit spt` and `mlstring`.
`GENLIST f n` is represented by `(List.range n).map f`. -/
def callArgConvention {width : Nat} : WordLangProg (BitVec width) -> Bool
  | .inst value => instArgConvention value
  | .return _ values => values == (List.range values.length).map (fun x => 2 * (x + 1))
  | .raise exception => exception == 2
  | .install ptr len _ _ _ => ptr == 2 && len == 4
  | .ffi _ configuration configurationLength array arrayLength _ =>
      configuration == 2 && configurationLength == 4 &&
        array == 6 && arrayLength == 8
  | .alloc destination _ => destination == 2
  | .storeConsts a b c d _ => a == 0 && b == 2 && c == 4 && d == 6
  | .call returns _ arguments handler =>
      (match returns with
        | none => arguments == (List.range arguments.length).map (fun x => 2 * x)
        | some (returns, _, returnHandler, _, _) =>
            arguments == (List.range arguments.length).map (fun x => 2 * (x + 1)) &&
            returns == (List.range returns.length).map (fun x => 2 * (x + 1)) &&
            callArgConvention returnHandler &&
            (match handler with
              | none => true
              | some (value, handlerProg, _, _) =>
                  value == 2 && callArgConvention handlerProg))
  | .mustTerminate body => callArgConvention body
  | .seq first second => callArgConvention first && callArgConvention second
  | .loop _ body _ => callArgConvention body
  | .ite _ _ _ thenBranch elseBranch =>
      callArgConvention thenBranch && callArgConvention elseBranch
  | _ => true

/-- Exact HOL `wordConvs$call_arg_convention` over the faithful program
carrier. `GENLIST f n` is represented by `(List.range n).map f`. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "call_arg_convention_def"]
def callArgConventionHOL {width : Nat} : WordLangProgHOL (BitVec width) → Bool
  | .inst value => instArgConvention value
  | .return _ values => values == (List.range values.length).map (fun x => 2 * (x + 1))
  | .raise exception => exception == 2
  | .install ptr len _ _ _ => ptr == 2 && len == 4
  | .ffi _ configuration configurationLength array arrayLength _ =>
      configuration == 2 && configurationLength == 4 &&
        array == 6 && arrayLength == 8
  | .alloc destination _ => destination == 2
  | .storeConsts a b c d _ => a == 0 && b == 2 && c == 4 && d == 6
  | .call returns _ arguments handler =>
      (match returns with
        | none => arguments == (List.range arguments.length).map (fun x => 2 * x)
        | some (returns, _, returnHandler, _, _) =>
            arguments == (List.range arguments.length).map (fun x => 2 * (x + 1)) &&
            returns == (List.range returns.length).map (fun x => 2 * (x + 1)) &&
            callArgConventionHOL returnHandler &&
            (match handler with
              | none => true
              | some (value, handlerProg, _, _) =>
                  value == 2 && callArgConventionHOL handlerProg))
  | .mustTerminate body => callArgConventionHOL body
  | .seq first second => callArgConventionHOL first && callArgConventionHOL second
  | .loop _ body _ => callArgConventionHOL body
  | .ite _ _ _ thenBranch elseBranch =>
      callArgConventionHOL thenBranch && callArgConventionHOL elseBranch
  | _ => true

/-- HOL `ARB : memop`, represented by a fixed representative. Untagged
Flapjack-specific stand-in: `not_created_subprogs` cannot denote HOL's
arbitrary value directly. The `no_alloc`/`no_install`/`no_mt`/`no_share_inst`
specialisations below are invariant to this choice, because each only tests
its own constant. -/
def wordLangArbMemOp : WordMemOp := .load

/-- HOL `wordConvs$not_created_subprogs_def` (`wordConvsScript.sml:536-566`)
over the faithful backend WordLang syntax. `P` is `Prop`-valued (HOL's is
`Bool`): the `Alloc`/`Install` clauses compare against `(LN,LN)` and the
`ShareInst` clause against `ARB`, and `WordLangNumSet` has no decidable
equality. The recursion and every constructor clause match HOL. Untagged:
exact HOL statement shape is not claimed while the value is `Prop`. -/
def notCreatedSubprogs {width : Nat}
    (P : WordLangProg (BitVec width) → Prop) :
    WordLangProg (BitVec width) → Prop
  | .mustTerminate body => P (.mustTerminate .skip) ∧ notCreatedSubprogs P body
  | .seq first second =>
      notCreatedSubprogs P first ∧ notCreatedSubprogs P second
  | .loop _ body _ => notCreatedSubprogs P body
  | .ite _ _ _ thenBranch elseBranch =>
      notCreatedSubprogs P thenBranch ∧ notCreatedSubprogs P elseBranch
  | .call returns destination _arguments handler =>
      P (.call none destination [] none) ∧
        (match returns with
          | none => True
          | some (_, _, body, _, _) => notCreatedSubprogs P body) ∧
        (match handler with
          | none => True
          | some (_, body, label, _) =>
              P (.call none none [] (some (0, .skip, label, 0))) ∧
                notCreatedSubprogs P body)
  | .alloc _ _ => P (.alloc 0 ((FEMPTY : WordLangNumSet), (FEMPTY : WordLangNumSet)))
  | .locValue _ label => P (.locValue 0 label)
  | .shareInst _ _ _ => P (.shareInst wordLangArbMemOp 0 (.var 0))
  | .install _ _ _ _ _ =>
      P (.install 0 0 0 0 ((FEMPTY : WordLangNumSet), (FEMPTY : WordLangNumSet)))
  | _ => True

/-- HOL `wordConvs$no_alloc_subprogs_def`: `not_created_subprogs (λq. q ≠ Alloc 0 (LN,LN))`. -/
def noAllocSubprogs {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  notCreatedSubprogs
    (fun q => q ≠ .alloc 0 ((FEMPTY : WordLangNumSet), (FEMPTY : WordLangNumSet)))
    program

/-- HOL `wordConvs$no_install_subprogs_def`. -/
def noInstallSubprogs {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  notCreatedSubprogs
    (fun q => q ≠ .install 0 0 0 0 ((FEMPTY : WordLangNumSet), (FEMPTY : WordLangNumSet)))
    program

/-- HOL `wordConvs$no_mt_subprogs_def`. -/
def noMtSubprogs {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  notCreatedSubprogs (fun q => q ≠ .mustTerminate .skip) program

/-- HOL `wordConvs$no_share_inst_subprogs_def`. -/
def noShareInstSubprogs {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  notCreatedSubprogs
    (fun q => q ≠ .shareInst wordLangArbMemOp 0 (.var 0))
    program

/-! HOL `good_handlers_def` over the exact HOL-shaped WordLang carrier. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "good_handlers_def"]
def goodHandlersHOL {width : Nat} [NeZero width] (n : Nat) :
    WordLangProgHOL (BitVec width) -> Bool
  | .call returns _ _ handler =>
      match returns with
      | none => true
      | some (_, _, returnHandler, _, _) =>
          goodHandlersHOL n returnHandler &&
            (match handler with
             | some (_, handlerProg, handlerLabel, _) =>
                 handlerLabel == n && goodHandlersHOL n handlerProg
             | none => true)
  | .seq first second => goodHandlersHOL n first && goodHandlersHOL n second
  | .loop _ body _ => goodHandlersHOL n body
  | .ite _ _ _ thenBranch elseBranch =>
      goodHandlersHOL n thenBranch && goodHandlersHOL n elseBranch
  | .mustTerminate body => goodHandlersHOL n body
  | _ => true

/-- HOL `wordConvsScript$pre_alloc_conventions_def` (`wordConvsScript.sml:425-429`).
It asserts the pre-allocation convention on a backend program: every name in
the program's cut sets is a stack variable (`is_stack_var`), and the call
argument convention holds.  Untagged: it is built from the untagged
`everyStackVar`/`callArgConvention` (the `num_set` sub-terms use the audited
order-insensitive domain model of `docs/NUM-SET-AUDIT.md`). -/
def preAllocConventions {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  everyStackVar isStackVar program ∧ callArgConvention program

/-- HOL `wordConvsScript$post_alloc_conventions_def` (`wordConvsScript.sml:432-437`).
It asserts the post-allocation convention on a backend program: every register
is a physical register (`is_phy_var`), every name in the cut sets is at least
`2 * k`, and the call argument convention holds.  Untagged for the same reason
as `preAllocConventions`. -/
def postAllocConventions {width : Nat} (k : Nat) (program : WordLangProg (BitVec width)) : Prop :=
  everyVar isPhyVar program ∧
    everyStackVar (fun name => decide (name ≥ 2 * k)) program ∧
    callArgConvention program

end Flapjack
