import Flapjack.HolRef
import Flapjack.Pancake.PanToWord
import Flapjack.Compiler.Backend.WordToWord.Compile
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.WordDepth
import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.Semantics.TargetSem.State

/-! Exact source definition used by the final Pancake-to-target theorem.
This module assembles the native pass definitions and the original static
resource analysis; the full semantic theorem and production/API routing remain
separate obligations. -/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend

/-- Full original `compile_prog_max_def` (1147-1155). The machine state and
projection carriers remain independent arbitrary types, sharing only the
positive machine-word dimension with the source declarations.

The source program is passed directly to panToWord: this definition contains
no main-function reordering or synthesized default main. WordToStack uses the
literal false mode. Its returned stackFrameSize map feeds maxDepth at the
original InitGlobals label in the compiled WordToWord code. The original
backend configuration is passed unchanged to fromStack, with the empty native
name map and the actual bitmap/program outputs. Both result components retain
Option; no fallback bound or successful-target premise is introduced.

The returned coloring-oracle tail and frame list are retained as `_coloring`
and `_frames`, which the original definition binds but does not use. The
original proof theory is not compiled in the pinned oracle toolchain; the
registered probe replays the literal full source definition in a separate HOL
theory with all original pass dependencies loaded. Its complete inferred type
and equation are explicitly local source replays, not exported-theory captures
or a cross-language equivalence proof. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "compile_prog_max_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compileProgMax {width : Nat} [NeZero width]
    {State Projection : Type}
    (config : Flapjack.Compiler.Backend.Backend.Config)
    (machine : MachineConfig width State Projection)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) × Option Nat :=
  let asmConf := machine.target.config
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compile config.wordToWordConf asmConf program
  let (bitmaps, wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  let maximum := WordDepth.maxDepth wordConfig.stackFrameSize
    (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wordProgram))
  (Flapjack.Compiler.Backend.Backend.fromStack asmConf config .ln stackProgram bitmaps,
    maximum)

end Flapjack.Pancake.Proofs.PanToTarget
