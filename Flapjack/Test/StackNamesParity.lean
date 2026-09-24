import Flapjack.Compiler.Backend.StackNames

namespace Flapjack.Test.StackNamesParity

open Flapjack
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackNames

private abbrev W := BitVec 8

private abbrev PT :=
  Flapjack.Compiler.Backend.StackLang.Prog
    (WordLangInst W) Cmp (WordRegImm W) BinOp WordMemOp (WordLangAddr W) String

private def pSeq (first second : PT) : PT :=
  Flapjack.Compiler.Backend.StackLang.Prog.seq first second
private def pInst (instruction : WordLangInst W) : PT :=
  Flapjack.Compiler.Backend.StackLang.Prog.inst instruction
private def pHalt (register : Nat) : PT :=
  Flapjack.Compiler.Backend.StackLang.Prog.halt register
private def pRaise (exception : Nat) : PT :=
  Flapjack.Compiler.Backend.StackLang.Prog.raise exception
private def pCall (returnHandler : Option (PT × Nat × Nat × Nat)) (target : Sum Nat Nat)
    (handler : Option (PT × Nat × Nat)) : PT :=
  Flapjack.Compiler.Backend.StackLang.Prog.call returnHandler target handler
private def iConst (destination : Nat) (value : W) : WordLangInst W :=
  WordLangInst.const destination value
private def iArith (operation : WordLangArith W) : WordLangInst W :=
  WordLangInst.arith operation
private def iMem (operator : WordMemOp) (destination : Nat) (address : WordLangAddr W) : WordLangInst W :=
  WordLangInst.mem operator destination address
private def iFp (operation : WordLangFp) : WordLangInst W :=
  WordLangInst.fp operation
private def aDiv (a b c : Nat) : WordLangArith W := WordLangArith.div a b c
private def fFma (a b c : Nat) : WordLangFp := WordLangFp.fpFma a b c
private def dAddr (base : Nat) (offset : W) : WordLangAddr W := WordLangAddr.addr base offset
private def riReg (name : Nat) : WordRegImm W := WordRegImm.reg name
private def riImm (value : W) : WordRegImm W := WordRegImm.imm value

/-- Renaming map `3 |-> 7` (HOL oracle `sptree$insert 3 7 (sptree$LN)`). -/
private def names : FiniteMap Nat Nat := fun k => if k = 3 then some 7 else none

/-- Empty renaming map. -/
private def emptyNames : FiniteMap Nat Nat := fun _ => none

/-- Colliding map `0 |-> 1`, `1 |-> 1`. -/
private def dupNames : FiniteMap Nat Nat :=
  fun k => if k = 0 then some 1 else if k = 1 then some 1 else none

private def isReg7 : Bool :=
  match riFindName names (riReg 3) with
  | Flapjack.WordRegImm.reg 7 => true
  | _ => false

private def isConst7 : Bool :=
  match instFindName names (iConst 3 0) with
  | Flapjack.WordLangInst.const 7 _ => true
  | _ => false

private def isHalt7 (p : PT) : Bool :=
  match p with
  | Flapjack.Compiler.Backend.StackLang.Prog.halt 7 => true
  | _ => false

-- `ri_find_name`
example : riFindName names (riReg 3) = riReg 7 := rfl
example : riFindName names (riImm 0) = riImm 0 := rfl

-- `inst_find_name`
example : instFindName names (iConst 3 0) = iConst 7 0 := rfl
example : instFindName names (iArith (aDiv 3 4 5)) = iArith (aDiv 7 4 5) := rfl
example : instFindName names (iFp (fFma 1 2 3)) = iFp (fFma 1 2 3) := rfl
example : instFindName names (iMem .load 3 (dAddr 3 8)) = iMem .load 7 (dAddr 7 8) := rfl

-- `dest_find_name`
example : destFindName names (.inr 3 : Sum Nat Nat) = .inr 7 := rfl
example : destFindName names (.inl 2 : Sum Nat Nat) = .inl 2 := rfl

-- `comp` / `prog_comp` / `compile`
example : progComp names (pSeq (pInst (iConst 3 0)) (pHalt 3)) =
    pSeq (pInst (iConst 7 0)) (pHalt 7) := rfl
example : progComp names (pCall (some (pRaise 3, 4, 5, 6)) (.inr 3) (some (pHalt 4, 8, 9))) =
    pCall (some (pRaise 7, 4, 5, 6)) (.inr 7) (some (pHalt 4, 8, 9)) := rfl
example : progCompEntry names (1, pHalt 3) = (1, pHalt 7) := rfl
example : compile names [(1, pHalt 3), (2, pRaise 4)] =
    [(1, pHalt 7), (2, pRaise 4)] := rfl

-- `names_ok`
example : namesOk names 4 [0, 1] = false := rfl
example : namesOk emptyNames 8 [] = true := rfl
example : namesOk dupNames 4 [] = false := rfl
example : namesOkHOL emptyNames 8 [] :=
  (namesOkHOL_iff_bool _ _ _).2 (by rfl)
example : ¬namesOkHOL names 4 [0, 1] := by
  intro h
  have hb := (namesOkHOL_iff_bool _ _ _).1 h
  have hfalse : namesOk names 4 [0, 1] = false := by rfl
  simp [hfalse] at hb

private def mapFstSample : List (Nat × PT) := [(1, pHalt 3), (2, pRaise 4)]

-- `MAP_FST_compile`
example : (compile names mapFstSample).map Prod.fst = mapFstSample.map Prod.fst :=
  map_fst_compile names mapFstSample

private def parityGuard : Bool :=
  isReg7 && isConst7 &&
  (match destFindName names (.inr 3 : Sum Nat Nat) with | .inr 7 => true | _ => false) &&
  (namesOk names 4 [0, 1] == false) &&
  (namesOk emptyNames 8 [] == true) &&
  (namesOk dupNames 4 [] == false) &&
  ((compile names mapFstSample).map Prod.fst == mapFstSample.map Prod.fst) &&
  (match compile names [(1, pHalt 3)] with
   | [(1, p)] => isHalt7 p
   | _ => false)

#guard parityGuard

/-- The `stack_names` renaming port matches every direct HOL EVAL row. -/
def runChecks : IO Bool := do
  IO.println "PASS stack_names ri_find_name/inst_find_name/dest_find_name/comp/compile/names_ok match the HOL oracle"
  pure parityGuard

end Flapjack.Test.StackNamesParity
