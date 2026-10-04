import Flapjack.Pancake.Proofs.PanToTarget.CompileProgMax
import Flapjack.Compiler.Backend.WordToWord.ExecutableCompile

/-! Callable native maximum-stack API. This Flapjack computation infrastructure
uses the proved executable WordToWord composition; every other operation is
identical to the tagged source definition. It takes original native declarations
and configuration and computes both the compiler result and static bound from
actual lowering/frame results. Unknown remains none, independently of compiler
success. The bound uses the original stack-word units, with no byte conversion
or estimate for unknown graphs. No separately named HOL declaration is claimed for the replacement. -/
namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Pancake.PanLang Flapjack.Compiler.Backend

def compileProgMaxExecutable {width : Nat} [NeZero width]
    {State Projection : Type}
    (config : Flapjack.Compiler.Backend.Backend.Config)
    (machine : MachineConfig width State Projection)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) × Option Nat :=
  let asmConf := machine.target.config
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileExecutable config.wordToWordConf asmConf program
  let (bitmaps, wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  let maximum := WordDepth.maxDepth wordConfig.stackFrameSize
    (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wordProgram))
  (Flapjack.Compiler.Backend.Backend.fromStack asmConf config .ln stackProgram bitmaps,
    maximum)

/-- Unconditional native source agreement; state and projection types remain
independent and no successful compiler or target evaluation is assumed. -/
theorem compileProgMaxExecutable_eq {width : Nat} [NeZero width]
    {State Projection : Type} (config : Backend.Config)
    (machine : MachineConfig width State Projection)
    (program : List (DeclHOL width)) :
    compileProgMaxExecutable config machine program = compileProgMax config machine program := by
  simp only [compileProgMaxExecutable, compileProgMax, WordToWord.compileExecutable_eq]

end Flapjack.Pancake.Proofs.PanToTarget
