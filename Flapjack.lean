import Flapjack.Language
import Flapjack.PanSimp
import Flapjack.PanStructs
import Flapjack.PanGlobals
import Flapjack.Pipeline
import Flapjack.Correctness
import Flapjack.FlatCorrectness
import Flapjack.Tests
import Flapjack.Static
import Flapjack.Crepe
import Flapjack.PanToCrep
import Flapjack.Compile
import Flapjack.Semantics
import Flapjack.PanValues
import Flapjack.PanMemory
import Flapjack.RiscV.Model
import Flapjack.RiscV.PanMemory
import Flapjack.RiscV.PanSemantics
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Calls
import Flapjack.RiscV.CorrectnessFfi
import Flapjack.RiscV.Ffi
import Flapjack.RiscV.Link
import Flapjack.WordSemantics
import Flapjack.Loop
import Flapjack.CrepToLoop
import Flapjack.LoopAnalysis
import Flapjack.LoopSemantics
import Flapjack.Word

/-!
# Flapjack in Lean

The library currently contains the first Lean representation of Flapjack's
front-end language. The source of truth used while porting is the CakeML HOL
development in `cakeml/pancake`.
-/
