import Flapjack.Language
import Flapjack.Tests
import Flapjack.Static
import Flapjack.Crepe
import Flapjack.PanToCrep
import Flapjack.Compile
import Flapjack.Semantics
import Flapjack.RiscV.Model
import Flapjack.Loop
import Flapjack.CrepToLoop
import Flapjack.LoopAnalysis

/-!
# Flapjack in Lean

The library currently contains the first Lean representation of Flapjack's
front-end language. The source of truth used while porting is the CakeML HOL
development in `cakeml/pancake`.
-/
