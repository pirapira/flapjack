import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.FullInstructionValidity

/-!
# `word_allocProof`: SSA output has distinct target registers

HOL `fake_seq_every_inst_distinct_tar_reg`, `loop_setup_every_inst_distinct_tar_reg`,
`fake_moves_distinct_tar_reg`, `ssa_cc_trans_distinct_tar_reg` and
`full_ssa_cc_trans_distinct_tar_reg` (`word_allocProofScript.sml:10442-10982`).
SSA renames every written register to a fresh name above all source registers,
so no instruction writes one of its own operands. HOL's `every_inst
distinct_tar_reg` over `'a inst` reads each instruction through the reviewed
`HolInst.ofWordLangInst` mirror. The case structure follows the accepted
`ssa_cc_trans_full_inst_ok_less` port.
-/

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- HOL `fake_seq_every_inst_distinct_tar_reg` (`word_allocProofScript.sml:10442-10447`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "fake_seq_every_inst_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem fakeSeq_distinctTarReg {width : Nat} [NeZero width] (names : List Nat) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
      ((names.map (fakeMove : Nat → WordLangProgHOL (BitVec width))).foldr .seq .skip) = true := by
  induction names with
  | nil => simp [everyInst]
  | cons name names ih =>
      simpa [everyInst, fakeMove, HolInst.ofWordLangInst, distinctTarRegExact] using ih

/-- HOL `loop_setup_every_inst_distinct_tar_reg` (`word_allocProofScript.sml:10483-10493`),
with the producer equation as sole premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "loop_setup_every_inst_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem loopSetup_distinctTarReg {width : Nat} [NeZero width]
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat)
    (setupProg : WordLangProgHOL (BitVec width)) (ssaRefreshed : Spt Nat)
    (naRefreshed : Nat)
    (setup : loopSetup names exitNames ssa na = (setupProg, ssaRefreshed, naRefreshed)) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) setupProg = true := by
  unfold loopSetup at setup
  generalize hr : listNextVarRename
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isNone) ssa na = renamed at setup
  rcases renamed with ⟨fresh, extended, next⟩
  generalize hm : listNextVarRenameMove (width := width) extended next
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isSome) = moved at setup
  rcases moved with ⟨moves, refreshed, nextOut⟩
  simp only [hr, hm] at setup
  have fake := fakeSeq_distinctTarReg (width := width) fresh
  have moveConvention :
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) moves = true := by
    unfold listNextVarRenameMove at hm
    have projected := congrArg Prod.fst hm
    simp only at projected
    rw [← projected]
    simp [everyInst]
  have output := congrArg Prod.fst setup
  simp only at output
  rw [← output]
  simp only [everyInst, fake, moveConvention, Bool.and_self]

/-- HOL `fake_moves_distinct_tar_reg` (`word_allocProofScript.sml:10777-10787`); HOL's free
`prio` is the leading binder. HOL's binder `conf` does not occur in the statement and is
omitted. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "fake_moves_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem fakeMoves_distinctTarReg {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    ∀ (ls : List Nat) (ssal ssar : Spt Nat) (na : Nat) (l r : WordLangProgHOL (BitVec width))
      (a : Nat) (b c : Spt Nat),
      fakeMoves prio ls ssal ssar na = (l, r, a, b, c) →
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) l = true ∧
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) r = true := by
  intro ls ssal ssar na l r a b c produced
  -- the configuration of `fake_moves_conventions2` is irrelevant to these conjuncts
  let config : AsmConfigExact width :=
    { isa := .riscv, encode := fun _ => [], bigEndian := false, codeAlignment := 0,
      linkReg := none, avoidRegs := [], regCount := 0, fpRegCount := 0, twoRegArith := false,
      validImm := fun _ _ => true, addrOffset := (0, 0), hwOffset := (0, 0),
      byteOffset := (0, 0), jumpOffset := (0, 0), cjumpOffset := (0, 0), locOffset := (0, 0) }
  have facts := fakeMoves_instructionConventions config prio ls ssal ssar na l r a b c produced
  exact ⟨facts.2.2.1, facts.2.2.2⟩

/-- Flapjack factoring of source register-bound monotonicity; no separately
named original. -/
private theorem boundMore {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (old next : Nat) (increase : old ≤ next)
    (bound : everyVarHOL (fun x => decide (x < old)) program = true) :
    everyVarHOL (fun x => decide (x < next)) program = true := by
  apply everyVarMono _ program _
  refine ⟨?_, bound⟩
  intro x hx
  simp only [decide_eq_true_eq] at hx ⊢
  omega

/-- Flapjack factoring of the original reconciliation proof; no separately
named HOL declaration. -/
private theorem fix_distinct {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    let (a, b, _, _) := fixInconsistencies (width := width) prio l r next
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) a = true ∧
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) b = true := by
  unfold fixInconsistencies
  generalize hm : mergeMoves ((sptToAList (sptUnion l r)).map Prod.fst) l r next = merged
  rcases merged with ⟨lmov, rmov, count, left, right⟩
  generalize hf : fakeMoves (width := width) prio ((sptToAList (sptUnion l r)).map Prod.fst)
    left right count = result
  rcases result with ⟨a, b, final, leftOut, rightOut⟩
  have facts := fakeMoves_distinctTarReg prio _ left right count a b final leftOut rightOut hf
  simpa [hm, hf, everyInst] using facts

/-- Flapjack factoring of literal Skip/Move reconciliation; no separate original. -/
private theorem distinct_reconcile {width : Nat} [NeZero width] {β : Type}
    (current target : Spt Nat) (names : Spt β) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
      (ssaReconcile (width := width) current target names) = true := by
  unfold ssaReconcile
  dsimp only
  split <;> simp [everyInst]

/-- HOL `ssa_cc_trans_distinct_tar_reg`, `Inst` case: the destination is the
fresh `na`, above every renamed source register. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_distinctInst {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ everyVarHOL (fun x => decide (x < next)) (.inst instruction) = true ∧
      ssaMapOK next ssa) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
      (ssaCcTrans (.inst instruction) ssa next tables).1 = true := by
  have allocated := h.1
  have positive : 0 < next := by
    simp only [isAllocVar, decide_eq_true_eq] at allocated
    omega
  have lookupBound : ∀ key, optionLookup ssa key < next := by
    intro key
    unfold optionLookup
    cases found : sptLookup key ssa with
    | none => simpa using positive
    | some value => exact (h.2.2 key value found).2
  have lookupNe : ∀ key, next ≠ optionLookup ssa key :=
    fun key => Nat.ne_of_gt (lookupBound key)
  have lookupNeReverse : ∀ key, optionLookup ssa key ≠ next :=
    fun key => (lookupNe key).symm
  have alloc : next % 4 = 1 := by simpa [isAllocVar] using allocated
  simp only [ssaCcTrans]
  rcases instruction with _ | ⟨reg, w⟩ | a | ⟨op, r, ad⟩ | f
  · simp [ssaCcTransInst, everyInst]
  · simp [ssaCcTransInst, nextVarRename, everyInst, HolInst.ofWordLangInst, distinctTarRegExact]
  · cases a with
    | binop bop r1 r2 ri =>
      cases ri <;> simp +zetaDelta [ssaCcTransInst, nextVarRename, everyInst, HolInst.ofWordLangInst,
        HolArith.ofWordLangArith, HolRegImm.ofWordRegImm, distinctTarRegExact, lookupNeReverse]
    | shift sh r1 r2 ri =>
      cases ri with
      | reg r3 =>
        simp +zetaDelta [ssaCcTransInst, nextVarRename, everyInst, HolInst.ofWordLangInst,
          HolArith.ofWordLangArith, HolRegImm.ofWordRegImm, distinctTarRegExact]
        omega
      | imm w =>
        simp +zetaDelta [ssaCcTransInst, nextVarRename, everyInst, HolInst.ofWordLangInst,
          HolArith.ofWordLangArith, HolRegImm.ofWordRegImm, distinctTarRegExact]
    | _ =>
      simp +zetaDelta only [ssaCcTransInst, nextVarRename]
      simp_all +zetaDelta [everyInst, HolInst.ofWordLangInst, HolArith.ofWordLangArith,
        distinctTarRegExact] <;> omega
  · cases op <;> cases ad <;> simp +zetaDelta [ssaCcTransInst, nextVarRename, everyInst,
      HolInst.ofWordLangInst, distinctTarRegExact]
  · cases f <;> simp +zetaDelta only [ssaCcTransInst, nextVarRename] <;> (repeat' split) <;>
      simp [everyInst, HolInst.ofWordLangInst, distinctTarRegExact]

/-- HOL `ssa_cc_trans_distinct_tar_reg`, `OpCurrHeap` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_distinctOpCurrHeap {width : Nat} [NeZero width]
    (operator : BinOp) (destination source : Nat)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next))
        (.opCurrHeap operator destination source : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
      (ssaCcTrans (.opCurrHeap operator destination source : WordLangProgHOL (BitVec width))
        ssa next tables).1 = true := by
  have allocated := h.1
  have positive : 0 < next := by
    simp only [isAllocVar, decide_eq_true_eq] at allocated
    omega
  have lookupBound : optionLookup ssa source < next := by
    unfold optionLookup
    cases found : sptLookup source ssa with
    | none => simpa using positive
    | some value => exact (h.2.2 source value found).2
  simp only [ssaCcTrans, nextVarRename, everyInst, HolInst.ofWordLangInst,
    HolArith.ofWordLangArith, HolRegImm.ofWordRegImm, distinctTarRegExact]
  simp only [decide_eq_true_eq]
  omega

/-- HOL `ssa_cc_trans_distinct_tar_reg`, `If` case, with the two structurally
generalized branch induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_distinctIf {width : Nat} [NeZero width]
    (cmp : Cmp) (condition : Nat) (right : WordRegImm (BitVec width))
    (yes no : WordLangProgHOL (BitVec width))
    (yesIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ everyVarHOL (fun x => decide (x < next)) yes = true ∧ ssaMapOK next ssa →
        everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
          (ssaCcTrans yes ssa next tables).1 = true)
    (noIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ everyVarHOL (fun x => decide (x < next)) no = true ∧ ssaMapOK next ssa →
        everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
          (ssaCcTrans no ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.ite cmp condition right yes no) = true ∧
      ssaMapOK next ssa) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
      (ssaCcTrans (.ite cmp condition right yes no) ssa next tables).1 = true := by
  have bounds := h.2.1
  simp only [everyVarHOL, Bool.and_eq_true] at bounds
  generalize yesEq : ssaCcTrans yes ssa next tables = yesResult
  rcases yesResult with ⟨a, leftMap, nextA⟩
  have properties := ssaCcTransProps yes ssa next tables a leftMap nextA yesEq ⟨h.2.2, h.1⟩
  have ha := yesIH ssa next tables ⟨h.1, bounds.1.2, h.2.2⟩
  rw [yesEq] at ha
  have hb := noIH ssa nextA tables
    ⟨properties.2.1, boundMore no next nextA properties.1 bounds.2,
      ssaMapOKMore next ssa nextA ⟨h.2.2, properties.1⟩⟩
  generalize noEq : ssaCcTrans no ssa nextA tables = noResult
  rcases noResult with ⟨b, rightMap, nextB⟩
  rw [noEq] at hb
  have fixed := fix_distinct (width := width) (mkPrio a b) leftMap rightMap nextB
  generalize fixEq : fixInconsistencies (width := width) (mkPrio a b) leftMap rightMap nextB = fixResult
  rcases fixResult with ⟨leftFix, rightFix, finalNext, finalMap⟩
  rw [fixEq] at fixed
  simp only [ssaCcTrans, yesEq, noEq, fixEq, everyInst, Bool.and_eq_true]
  exact ⟨⟨ha, fixed.1⟩, hb, fixed.2⟩

/-- HOL `ssa_cc_trans_distinct_tar_reg`, `Loop` case (`Resume ...[Loop]`), with a
structurally generalized body induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_distinctLoop {width : Nat} [NeZero width]
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (bodyIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ everyVarHOL (fun x => decide (x < next)) body = true ∧ ssaMapOK next ssa →
        everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
          (ssaCcTrans body ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.loop names body exitNames) = true ∧
      ssaMapOK next ssa) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
      (ssaCcTrans (.loop names body exitNames) ssa next tables).1 = true := by
  have bounds := h.2.1
  simp only [everyVarHOL, Bool.and_eq_true] at bounds
  generalize setupEq : loopSetup (width := width) names exitNames ssa next = setupResult
  rcases setupResult with ⟨setup, refreshed, nextRefreshed⟩
  have properties := loopSetup_propsLocal names exitNames ssa next setup refreshed nextRefreshed
    ⟨setupEq, h.2.2, h.1⟩
  have setupPre := loopSetup_distinctTarReg names exitNames ssa next setup refreshed nextRefreshed
    setupEq
  have bodyPre := bodyIH (sptInter refreshed names) nextRefreshed
    ((refreshed, names, exitNames) :: tables)
    ⟨properties.1, boundMore body next nextRefreshed properties.2.2 bounds.1.2,
      ssaMapOKInter nextRefreshed refreshed names properties.2.1⟩
  generalize bodyEq : ssaCcTrans body (sptInter refreshed names) nextRefreshed
    ((refreshed, names, exitNames) :: tables) = bodyResult
  rcases bodyResult with ⟨output, bodyMap, nextOut⟩
  rw [bodyEq] at bodyPre
  have backPre := distinct_reconcile (width := width) bodyMap refreshed names
  generalize backEq : ssaReconcile (width := width) bodyMap refreshed names = back
  rw [backEq] at backPre
  cases back <;>
    simp only [ssaCcTrans, setupEq, bodyEq, backEq, everyInst, Bool.and_eq_true, and_true]
      at setupPre bodyPre backPre ⊢ <;>
    first | exact ⟨setupPre, bodyPre⟩ | exact ⟨setupPre, bodyPre, backPre⟩

/-- HOL `ssa_cc_trans_distinct_tar_reg`, returning `Call` case with both
exception-handler options and structurally generalized handler induction
hypotheses; handler map bounds are derived from the original producers. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_distinctReturningCall {width : Nat} [NeZero width]
    (ret : List Nat) (cutsets : WordLangCutsetsHOL)
    (retHandler : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (retIH : ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar next ∧ everyVarHOL (fun x => decide (x < next)) retHandler = true ∧
        ssaMapOK next ssa →
        everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
          (ssaCcTrans retHandler ssa next tables).1 = true)
    (handlerIH : match handler with
      | none => True
      | some (_, body, _, _) =>
        ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
          isAllocVar next ∧ everyVarHOL (fun x => decide (x < next)) body = true ∧
            ssaMapOK next ssa →
            everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
              (ssaCcTrans body ssa next tables).1 = true)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next))
        (.call (some (ret, cutsets, retHandler, l1, l2)) dest args handler) = true ∧
      ssaMapOK next ssa) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
      (ssaCcTrans (.call (some (ret, cutsets, retHandler, l1, l2)) dest args handler)
        ssa next tables).1 = true := by
  have returnBound : everyVarHOL (fun x => decide (x < next)) retHandler = true := by
    have bound := h.2.1
    cases handler with
    | none => simp only [everyVarHOL, Bool.and_eq_true] at bound; aesop
    | some exc =>
        rcases exc with ⟨name, body, l1, l2⟩
        simp only [everyVarHOL, Bool.and_eq_true] at bound
        aesop
  let allNames := sptUnion cutsets.1 cutsets.2
  let keys := (sptToAList allNames).map Prod.fst
  generalize stackEq : listNextVarRenameMove (width := width) ssa (next + 2) keys = stacked
  rcases stacked with ⟨stackMov, stackTree, stackCounter⟩
  have stackFrame := listNextVarRenameMoveProps2 keys ssa next stackMov stackTree stackCounter
    stackEq ⟨Or.inl h.1, h.2.2⟩
  have stackClass := stackFrame.2.1 h.1
  have cutFrame := ssaMapOKInter stackCounter stackTree allNames stackFrame.2.2.2
  have stackPre : everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) stackMov = true := by
    have := congrArg Prod.fst stackEq
    simp only [listNextVarRenameMove] at this
    rw [← this]; rfl
  generalize retEq : listNextVarRenameMove (width := width)
    (sptInter stackTree allNames) (stackCounter + 2) keys = returned
  rcases returned with ⟨retMov, retTree, retCounter⟩
  have retFrame := listNextVarRenameMoveProps2 keys (sptInter stackTree allNames) stackCounter
    retMov retTree retCounter retEq ⟨Or.inr stackClass, cutFrame⟩
  have retClass := retFrame.2.2.1 stackClass
  have retPre : everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) retMov = true := by
    have := congrArg Prod.fst retEq
    simp only [listNextVarRenameMove] at this
    rw [← this]; rfl
  generalize rawEq : listNextVarRename ret retTree retCounter = raw
  rcases raw with ⟨retRegisters, retInputTree, retInputCounter⟩
  have rawFrame := listNextVarRenameProps ret retTree retCounter retRegisters retInputTree
    retInputCounter rawEq ⟨Or.inl retClass, retFrame.2.2.2⟩
  have bodyPre := retIH retInputTree retInputCounter tables
    ⟨rawFrame.2.1 retClass,
      boundMore retHandler next retInputCounter
        (by have a := stackFrame.1; have b := retFrame.1; have c := rawFrame.1; omega) returnBound,
      rawFrame.2.2.2⟩
  generalize bodyEq : ssaCcTrans retHandler retInputTree retInputCounter tables = body
  rcases body with ⟨renRetHandler, retOutTree, retOutCounter⟩
  rw [bodyEq] at bodyPre
  have bodyFrame := ssaCcTransProps retHandler retInputTree retInputCounter tables
    renRetHandler retOutTree retOutCounter bodyEq ⟨rawFrame.2.2.2, rawFrame.2.1 retClass⟩
  let regs := (List.range ret.length).map (fun x => 2 * (x + 1))
  let movRetHandler : WordLangProgHOL (BitVec width) :=
    .seq retMov (.seq (.move 1 (retRegisters.zip regs)) renRetHandler)
  have returnPre :
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) movRetHandler = true := by
    simp [movRetHandler, everyInst, retPre, bodyPre]
  cases handler with
  | none =>
      dsimp only [keys, allNames] at stackEq retEq
      simp only [ssaCcTrans, stackEq, retEq, rawEq, bodyEq]
      simp only [movRetHandler, everyInst, Bool.and_eq_true] at returnPre ⊢
      simp_all
  | some exc =>
      rcases exc with ⟨name, excHandler, excL1, excL2⟩
      have excBound : everyVarHOL (fun x => decide (x < next)) excHandler = true := by
        have bound := h.2.1
        simp only [everyVarHOL, Bool.and_eq_true] at bound
        aesop
      have retTreeLater := ssaMapOKMore retCounter retTree retOutCounter
        ⟨retFrame.2.2.2, Nat.le_trans rawFrame.1 bodyFrame.1⟩
      generalize freshEq : nextVarRename name retTree retOutCounter = fresh
      rcases fresh with ⟨freshLabel, freshTree, freshCounter⟩
      have freshFrame := nextVarRenameProps name retTree retOutCounter freshLabel freshTree
        freshCounter freshEq ⟨Or.inl bodyFrame.2.1, retTreeLater⟩
      have excPre := handlerIH freshTree freshCounter tables
        ⟨freshFrame.2.1 bodyFrame.2.1,
          boundMore excHandler next freshCounter
            (by have a := stackFrame.1; have b := retFrame.1; have c := rawFrame.1;
                have d := bodyFrame.1; have e := freshFrame.1; omega) excBound,
          freshFrame.2.2.2⟩
      generalize excEq : ssaCcTrans excHandler freshTree freshCounter tables = excBody
      rcases excBody with ⟨renExcHandler, excOutTree, excOutCounter⟩
      rw [excEq] at excPre
      let movExcHandler : WordLangProgHOL (BitVec width) :=
        .seq retMov (.seq (.move 1 [(freshLabel, 2)]) renExcHandler)
      have exceptionPre :
          everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) movExcHandler = true := by
        simp [movExcHandler, everyInst, retPre, excPre]
      have fixed := fix_distinct (width := width) (mkPrio movRetHandler movExcHandler)
        retOutTree excOutTree excOutCounter
      generalize fixEq : fixInconsistencies (width := width) (mkPrio movRetHandler movExcHandler)
        retOutTree excOutTree excOutCounter = fixResult
      rcases fixResult with ⟨leftFix, rightFix, finalNext, finalMap⟩
      rw [fixEq] at fixed
      dsimp only [keys, allNames] at stackEq retEq
      simp only [ssaCcTrans, stackEq, retEq, rawEq, bodyEq, freshEq, excEq]
      simp only [regs, movRetHandler, movExcHandler] at fixEq returnPre exceptionPre
      rw [fixEq]
      simp only [everyInst, Bool.and_eq_true] at returnPre exceptionPre fixed ⊢
      simp_all

/-- Flapjack factoring of the generalized structural induction motive; no
separately named HOL original. -/
private def programDistinct {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
    isAllocVar next ∧ everyVarHOL (fun x => decide (x < next)) prog = true ∧ ssaMapOK next ssa →
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
        (ssaCcTrans prog ssa next tables).1 = true

/-- HOL `ssa_cc_trans_distinct_tar_reg` (`word_allocProofScript.sml:10789-10951`, with its `Resume` cases),
assembled by structural induction including both nested handlers; only HOL's
allocation-class, source register bound and SSA map premises are assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_distinctTarReg {width : Nat} [NeZero width] :
    ∀ (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (na : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      isAllocVar na ∧ everyVarHOL (fun x => decide (x < na)) prog = true ∧ ssaMapOK na ssa →
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
        (ssaCcTrans prog ssa na lt).1 = true := by
  intro p
  apply WordLangProgHOL.rec
    (motive_1 := programDistinct)
    (motive_2 := fun ret => match ret with | none => True | some r => programDistinct r.2.2.1)
    (motive_3 := fun exc => match exc with | none => True | some r => programDistinct r.2.1)
    (motive_4 := fun r => programDistinct r.2.2.1)
    (motive_5 := fun r => programDistinct r.2.1)
    (motive_6 := fun r => programDistinct r.2.1)
    (motive_7 := fun r => programDistinct r.1) (t := p)
  case inst => intro instruction; exact ssaCcTrans_distinctInst instruction
  case opCurrHeap =>
    intro operator destination source; exact ssaCcTrans_distinctOpCurrHeap operator destination source
  case ite =>
    intro cmp condition right yes no yesIH noIH
    exact ssaCcTrans_distinctIf cmp condition right yes no yesIH noIH
  case loop =>
    intro names body exitNames bodyIH
    exact ssaCcTrans_distinctLoop names exitNames body bodyIH
  case seq =>
    intro first second firstIH secondIH ssa next tables h
    have bounds : everyVarHOL (fun x => decide (x < next)) first = true ∧
        everyVarHOL (fun x => decide (x < next)) second = true := by
      simpa only [everyVarHOL, Bool.and_eq_true] using h.2.1
    generalize firstEq : ssaCcTrans first ssa next tables = firstResult
    rcases firstResult with ⟨a, middle, nextA⟩
    have properties := ssaCcTransProps first ssa next tables a middle nextA firstEq ⟨h.2.2, h.1⟩
    have ha := firstIH ssa next tables ⟨h.1, bounds.1, h.2.2⟩
    rw [firstEq] at ha
    have hb := secondIH middle nextA tables
      ⟨properties.2.1, boundMore second next nextA properties.1 bounds.2, properties.2.2⟩
    generalize secondEq : ssaCcTrans second middle nextA tables = secondResult
    rcases secondResult with ⟨b, final, nextB⟩
    rw [secondEq] at hb
    simp only [ssaCcTrans, firstEq, secondEq, everyInst, ha, hb, Bool.and_self]
  case mustTerminate =>
    intro body bodyIH ssa next tables h
    have result := bodyIH ssa next tables ⟨h.1, by simpa only [everyVarHOL] using h.2.1, h.2.2⟩
    generalize produced : ssaCcTrans body ssa next tables = output
    rcases output with ⟨target, map, counter⟩
    rw [produced] at result
    simpa [ssaCcTrans, produced, everyInst] using result
  case «break» =>
    intro index ssa next tables _
    cases selected : tables[index]? with
    | none => simp [ssaCcTrans, selected, everyInst]
    | some entry =>
        rcases entry with ⟨target, names, exits⟩
        have pre := distinct_reconcile (width := width) ssa target exits
        generalize eq : ssaReconcile (width := width) ssa target exits = back
        rw [eq] at pre
        simp only [ssaCcTrans, selected, eq]
        cases back <;> simp_all [everyInst]
  case «continue» =>
    intro index ssa next tables _
    cases selected : tables[index]? with
    | none => simp [ssaCcTrans, selected, everyInst]
    | some entry =>
        rcases entry with ⟨target, names, exits⟩
        have pre := distinct_reconcile (width := width) ssa target names
        generalize eq : ssaReconcile (width := width) ssa target names = back
        rw [eq] at pre
        simp only [ssaCcTrans, selected, eq]
        cases back <;> simp_all [everyInst]
  case call =>
    intro returns dest args handler retIH excIH
    cases returns with
    | none => intro ssa next tables _; simp [ssaCcTrans, everyInst]
    | some ret =>
      rcases ret with ⟨ret, cutsets, retHandler, l1, l2⟩
      apply ssaCcTrans_distinctReturningCall ret cutsets retHandler l1 l2 dest args handler retIH
      cases handler with
      | none => exact True.intro
      | some exc =>
        rcases exc with ⟨name, body, l1, l2⟩
        exact excIH
  case none => exact True.intro
  case some => intro value ih; exact ih
  case none => exact True.intro
  case some => intro value ih; exact ih
  case mk => intro fst snd ih; exact ih
  case mk => intro fst snd ih; exact ih
  case mk => intro fst snd ih; exact ih
  case mk => intro body rest ih; exact ih
  all_goals
    dsimp only [programDistinct]
    intros
    simp [ssaCcTrans, everyInst, nextVarRename, listNextVarRenameMove]
    try (split <;> simp [everyInst])

/-- HOL `full_ssa_cc_trans_distinct_tar_reg` (`word_allocProofScript.sml:10953-10982`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "full_ssa_cc_trans_distinct_tar_reg" (words_as_type_indexed_bitvec)]
theorem fullSsaCcTrans_distinctTarReg {width : Nat} [NeZero width] :
    ∀ (n : Nat) (prog : WordLangProgHOL (BitVec width)),
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i))
        (fullSsaCcTrans n prog) = true := by
  intro count program
  have limitProps := limitVarProps program (limitVar program) rfl
  have setup := setupSSAProps2 (limitVar program) count program limitProps.1
  generalize produced : setupSSA (outputWidth := width) count (limitVar program) program = result
  rcases result with ⟨move, ssa, next⟩
  rw [produced] at setup
  have bound : everyVarHOL (fun x => decide (x < next)) program = true := by
    apply everyVarMono _ program _
    refine ⟨?_, limitProps.2⟩
    intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    have increase := setup.2.2.2
    omega
  have bodyDistinct := ssaCcTrans_distinctTarReg program ssa next [] ⟨setup.2.1, bound, setup.1⟩
  have moveDistinct :
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) move = true := by
    unfold setupSSA at produced
    generalize listNextVarRename (evenList count) .ln (limitVar program) = renamed at produced
    rcases renamed with ⟨names, tree, counter⟩
    cases produced
    rfl
  generalize bodyEq : ssaCcTrans program ssa next [] = bodyResult
  rcases bodyResult with ⟨body, finalMap, finalNext⟩
  rw [bodyEq] at bodyDistinct
  simp only [fullSsaCcTrans, produced, bodyEq, everyInst, moveDistinct, bodyDistinct, Bool.and_self]

end Flapjack.WordAlloc
