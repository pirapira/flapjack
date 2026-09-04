# Flapjack

Flapjack is beginning as a Lean 4 port of the formally verified Pancake
compiler. It is an early-stage project: the current Lean code covers the
front-end syntax and checking foundations, the first Pancake-to-Crepe and
Crepe-to-Loop compiler slices, executable semantic fragments, and an initial
RISC-V model. The CakeML HOL development is included as the `cakeml`
submodule; its Pancake sources are in [`cakeml/pancake`](cakeml/pancake).

The Lean library currently contains the core Pancake syntax in
[`Flapjack/Language.lean`](Flapjack/Language.lean) and the static-checker
data/context layer plus shape-aware core expression and structured-program
checkers in [`Flapjack/Static.lean`](Flapjack/Static.lean), as well as
the Crepe IR and expression lowerer in [`Flapjack/Crepe.lean`](Flapjack/Crepe.lean)
and [`Flapjack/PanToCrep.lean`](Flapjack/PanToCrep.lean).
Core structured statement lowering and top-level function assembly are in
[`Flapjack/Compile.lean`](Flapjack/Compile.lean).
The first executable local/memory semantics and preservation lemmas are in
[`Flapjack/Semantics.lean`](Flapjack/Semantics.lean).
The Loop intermediate language and the initial Crepe-to-Loop structural
lowering are in [`Flapjack/Loop.lean`](Flapjack/Loop.lean) and
[`Flapjack/CrepToLoop.lean`](Flapjack/CrepToLoop.lean). The latter keeps the
Loop vocabulary aligned with CakeML while making conversions that require
temporary allocation or control-flow lowering explicit as `Fail`.
The first Loop data-flow analyses are in
[`Flapjack/LoopAnalysis.lean`](Flapjack/LoopAnalysis.lean).
The initial RISC-V target vocabulary, register/memory primitives, and
`ADD`/`ADDI` transition slice are in [`Flapjack/RiscV/Model.lean`](Flapjack/RiscV/Model.lean),
with the HOL notice in [`Flapjack/RiscV/COPYRIGHT`](Flapjack/RiscV/COPYRIGHT).

Build it with:

```sh
lake build
```

The staged port is documented in [`PLAN.md`](PLAN.md).
