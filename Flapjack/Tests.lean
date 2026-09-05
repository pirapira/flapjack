import Flapjack.Test.Basics
import Flapjack.Test.SourceSemantics
import Flapjack.Test.SourceDeclarations
import Flapjack.Test.Compile
import Flapjack.Test.RiscVMemory
import Flapjack.Test.RiscV
import Flapjack.Test.Pipeline
import Flapjack.Test.Calls
import Flapjack.Test.Loops
import Flapjack.Test.Primitive
import Flapjack.Test.Allocator
import Flapjack.Test.AllocatorFunction
import Flapjack.Test.AllocatorCorrectness
import Flapjack.Test.AllocatorRegAlloc
import Flapjack.Test.WordToStack
import Flapjack.Test.ParallelMove
import Flapjack.RiscV.Correctness
import Flapjack.RiscV.CorrectnessFfi
import Flapjack.Test.Structured
import Flapjack.Test.CorrectnessFfi
import Flapjack.Test.CorrectnessCalls
import Flapjack.Test.CorrectnessMemory
import Flapjack.Test.CorrectnessPrimitive
import Flapjack.Test.CorrectnessControl
import Flapjack.Test.CorrectnessLoopHandlers
import Flapjack.Test.CorrectnessLoopControl
import Flapjack.Test.CorrectnessLoopCalls
import Flapjack.Test.CorrectnessLoopCallHandlers
import Flapjack.Test.CorrectnessLoopRepeat
import Flapjack.Test.WordLoopHandlers
import Flapjack.Test.CorrectnessFfiMachine
import Flapjack.Test.CorrectnessTarget
import Flapjack.Test.CrepCalls
import Flapjack.Test.CrepeSemantics
import Flapjack.Test.Ffi
import Flapjack.Test.LoopFfi
import Flapjack.Test.Stack
import Flapjack.Test.Lab
import Flapjack.Test.RiscVLab
import Flapjack.Test.StackRemove
import Flapjack.Test.StackRemoveCorrectness

/-!
# Flapjack regression tests

The tests are split by compiler layer under `Flapjack.Test`; importing this
module runs the complete regression suite while keeping each file reviewable.
-/
