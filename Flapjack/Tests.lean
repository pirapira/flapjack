import Flapjack.Test.Basics
import Flapjack.Test.Compile
import Flapjack.Test.RiscVMemory
import Flapjack.Test.RiscV
import Flapjack.Test.Pipeline
import Flapjack.Test.Calls
import Flapjack.Test.Loops
import Flapjack.Test.Primitive
import Flapjack.Test.Allocator
import Flapjack.RiscV.Correctness
import Flapjack.RiscV.CorrectnessFfi
import Flapjack.Test.Structured
import Flapjack.Test.CorrectnessFfi

/-!
# Flapjack regression tests

The tests are split by compiler layer under `Flapjack.Test`; importing this
module runs the complete regression suite while keeping each file reviewable.
-/
