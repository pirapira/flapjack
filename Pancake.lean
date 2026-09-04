import Pancake.Language
import Pancake.Tests
import Pancake.Static
import Pancake.Crepe
import Pancake.PanToCrep
import Pancake.Compile
import Pancake.Semantics
import Pancake.RiscV.Model
import Pancake.Loop
import Pancake.CrepToLoop
import Pancake.LoopAnalysis

/-!
# Pancake in Lean

The library currently contains the first Lean representation of Pancake's
front-end language. The source of truth used while porting is the CakeML HOL
development in `cakeml/pancake`.
-/
