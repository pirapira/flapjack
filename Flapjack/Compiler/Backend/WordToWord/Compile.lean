import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordToWord.Config
import Flapjack.Compiler.Backend.WordSimp
import Flapjack.Compiler.Backend.WordInst
import Flapjack.Compiler.Backend.WordAlloc.FullSSA
import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
import Flapjack.Compiler.Backend.WordCse.Transform
import Flapjack.Compiler.Backend.WordCopy
import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.Compiler.Backend.WordAlloc.WordAllocDef
import Flapjack.Compiler.Backend.WordRemove
import Flapjack.Pancake.WordLang.MaxVar

/-!
# `word_to_word` pass composition

The `word_to_wordScript.sml` definitions composing the wordLang passes over the
tagged native pass definitions: `compile_single`, `full_compile_single` and
`compile`. These are the proof-side definitions; the executed compiler is not
routed through them (production routing is tracked separately).
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `compile_single_def` (`word_to_wordScript.sml:21-35`): one
function body through word_simp, inst_select, SSA, remove_dead, CSE, copy
propagation, three-to-two registers, remove_unreach, remove_dead and the
register allocator. -/
@[hol "cakeml/compiler/backend/word_to_wordScript.sml" "compile_single_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compileSingle {width : Nat} [NeZero width] (twoRegArith : Bool)
    (regCount alg : Nat) (c : AsmConfigExact width)
    (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    Nat × Nat × WordLangProgHOL (BitVec width) :=
  let ((nameNum, argCount, prog), colOpt) := p
  let prog := WordSimp.compileExp prog
  let maxv := maxVarHOL prog + 1
  let instProg := WordInst.instSelect c maxv prog
  let ssaProg := WordAlloc.fullSsaCcTrans argCount instProg
  let rmSsaProg := WordAlloc.removeDeadProg ssaProg
  let cseProg := WordCse.wordCommonSubexpElim rmSsaProg
  let cpProg := WordCopy.copyProp cseProg
  let twoProg := WordInst.threeToTwoRegProg twoRegArith cpProg
  let unreachProg := WordUnreach.removeUnreach twoProg
  let rmProg := WordAlloc.removeDeadProg unreachProg
  let regProg := WordAlloc.wordAlloc nameNum c alg regCount rmProg colOpt
  (nameNum, argCount, regProg)

/-- Exact HOL `full_compile_single_def` (`word_to_wordScript.sml:37-41`):
`compile_single` followed by `remove_must_terminate`. -/
@[hol "cakeml/compiler/backend/word_to_wordScript.sml" "full_compile_single_def"
  (words_as_type_indexed_bitvec)]
noncomputable def fullCompileSingle {width : Nat} [NeZero width] (twoRegArith : Bool)
    (regCount alg : Nat) (c : AsmConfigExact width)
    (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    Nat × Nat × WordLangProgHOL (BitVec width) :=
  let (nameNum, argCount, regProg) := compileSingle twoRegArith regCount alg c p
  (nameNum, argCount, WordRemove.removeMustTerminate regProg)

/-- Exact HOL `compile_def` (`word_to_wordScript.sml:51-57`). HOL `ZIP` is
specified only on equal-length lists; `nextNOracle_length` gives exactly that
here, where `List.zip` coincides with it. The register count is HOL's
truncated `num` subtraction. -/
@[hol "cakeml/compiler/backend/word_to_wordScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compile {width : Nat} [NeZero width] (wordConf : Config)
    (asmConf : AsmConfigExact width) (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    List (Option (Spt Nat)) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  let (twoRegArith, regCount) :=
    (asmConf.twoRegArith, asmConf.regCount - (5 + asmConf.avoidRegs.length))
  let (nOracles, col) := nextNOracle progs.length wordConf.colOracle
  let progs := progs.zip nOracles
  (col, progs.map (fullCompileSingle twoRegArith regCount wordConf.regAlg asmConf))

/-- The oracle prefix consumed by `compile` has exactly one entry per
function, so the `ZIP` is between equal-length lists (Flapjack infrastructure,
derived inline in HOL). -/
theorem compile_zip_length {width : Nat} [NeZero width] (wordConf : Config)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    (nextNOracle progs.length wordConf.colOracle).1.length = progs.length :=
  nextNOracle_length _ _

end Flapjack.Compiler.Backend.WordToWord
