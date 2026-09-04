import Flapjack.Language
import Flapjack.PanSimp
import Flapjack.PanStructs
import Flapjack.PanGlobals
import Flapjack.Tests
import Flapjack.Static
import Flapjack.Crepe
import Flapjack.PanToCrep
import Flapjack.Compile
import Flapjack.Semantics
import Flapjack.RiscV.Model
import Flapjack.RiscV.Backend
import Flapjack.Loop
import Flapjack.CrepToLoop
import Flapjack.LoopAnalysis
import Flapjack.Word

/-!
# Flapjack in Lean

The library currently contains the first Lean representation of Flapjack's
front-end language. The source of truth used while porting is the CakeML HOL
development in `cakeml/pancake`.
-/
