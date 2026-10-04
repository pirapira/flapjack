import Flapjack.Compiler.Backend.WordToWord.Compile
import Flapjack.Compiler.Backend.WordInst.ExecutableInstSelect

/-! Flapjack executable computation infrastructure. Only the instruction selector
is replaced by its proved counterpart; tagged source types and bodies are unchanged. -/
namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.Compiler.Encoders.Asm

def compileSingleExecutable {width : Nat} [NeZero width] (twoRegArith : Bool)
    (regCount alg : Nat) (c : AsmConfigExact width)
    (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    Nat × Nat × WordLangProgHOL (BitVec width) :=
  let ((nameNum, argCount, prog), colOpt) := p
  let prog := WordSimp.compileExp prog
  let maxv := maxVarHOL prog + 1
  let instProg := WordInst.instSelectExecutable c maxv prog
  let ssaProg := WordAlloc.fullSsaCcTrans argCount instProg
  let rmSsaProg := WordAlloc.removeDeadProg ssaProg
  let cseProg := WordCse.wordCommonSubexpElim rmSsaProg
  let cpProg := WordCopy.copyProp cseProg
  let twoProg := WordInst.threeToTwoRegProg twoRegArith cpProg
  let unreachProg := WordUnreach.removeUnreach twoProg
  let rmProg := WordAlloc.removeDeadProg unreachProg
  let regProg := WordAlloc.wordAlloc nameNum c alg regCount rmProg colOpt
  (nameNum, argCount, regProg)

/-- Flapjack executable counterpart: compose the proved selector replacement
with the unchanged native must-terminate removal. No new HOL identity. -/
def fullCompileSingleExecutable {width : Nat} [NeZero width] (twoRegArith : Bool)
    (regCount alg : Nat) (c : AsmConfigExact width)
    (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    Nat × Nat × WordLangProgHOL (BitVec width) :=
  let (nameNum, argCount, regProg) := compileSingleExecutable twoRegArith regCount alg c p
  (nameNum, argCount, WordRemove.removeMustTerminate regProg)

/-- Flapjack executable composition infrastructure. The native oracle prefix,
ZIP inputs and truncated register subtraction are unchanged. -/
def compileExecutable {width : Nat} [NeZero width] (wordConf : Config)
    (asmConf : AsmConfigExact width) (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    List (Option (Spt Nat)) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  let (twoRegArith, regCount) :=
    (asmConf.twoRegArith, asmConf.regCount - (5 + asmConf.avoidRegs.length))
  let (nOracles, col) := nextNOracle progs.length wordConf.colOracle
  let progs := progs.zip nOracles
  (col, progs.map (fullCompileSingleExecutable twoRegArith regCount wordConf.regAlg asmConf))


theorem compileSingleExecutable_eq {width : Nat} [NeZero width] (two : Bool) (regs alg : Nat) (c : AsmConfigExact width) (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) : compileSingleExecutable two regs alg c p = compileSingle two regs alg c p := by
  simp only [compileSingleExecutable, compileSingle, WordInst.instSelectExecutable_eq]

theorem fullCompileSingleExecutable_eq {width : Nat} [NeZero width] (two : Bool) (regs alg : Nat) (c : AsmConfigExact width) (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) : fullCompileSingleExecutable two regs alg c p = fullCompileSingle two regs alg c p := by
  simp only [fullCompileSingleExecutable, fullCompileSingle, compileSingleExecutable_eq]

theorem compileExecutable_eq {width : Nat} [NeZero width] (conf : Config) (c : AsmConfigExact width) (ps : List (Nat × Nat × WordLangProgHOL (BitVec width))) : compileExecutable conf c ps = compile conf c ps := by
  simp only [compileExecutable, compile]
  congr 2
  funext p
  exact fullCompileSingleExecutable_eq _ _ _ _ p

end Flapjack.Compiler.Backend.WordToWord
