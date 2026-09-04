This project is an ongoing port of the Pancake compiler to Lean. The CakeML
HOL development is included as the `cakeml` submodule; its Pancake sources are
in [`cakeml/pancake`](cakeml/pancake).

The Lean library currently contains the core Pancake syntax in
[`Pancake/Language.lean`](Pancake/Language.lean) and the static-checker
data/context layer plus shape-aware core expression and structured-program
checkers in
[`Pancake/Static.lean`](Pancake/Static.lean), as well as
the Crepe IR and expression lowerer in [`Pancake/Crepe.lean`](Pancake/Crepe.lean)
and [`Pancake/PanToCrep.lean`](Pancake/PanToCrep.lean).
Core structured statement lowering and top-level function assembly are in
[`Pancake/Compile.lean`](Pancake/Compile.lean).
The first executable local/memory semantics and preservation lemmas are in
[`Pancake/Semantics.lean`](Pancake/Semantics.lean).
The Loop intermediate language and the initial Crepe-to-Loop structural
lowering are in [`Pancake/Loop.lean`](Pancake/Loop.lean) and
[`Pancake/CrepToLoop.lean`](Pancake/CrepToLoop.lean). The latter keeps the
Loop vocabulary aligned with CakeML while making conversions that require
temporary allocation or control-flow lowering explicit as `Fail`.
The first Loop data-flow analyses are in
[`Pancake/LoopAnalysis.lean`](Pancake/LoopAnalysis.lean).
The initial RISC-V target vocabulary, register/memory primitives, and
`ADD`/`ADDI` transition slice are in
[`Pancake/RiscV/Model.lean`](Pancake/RiscV/Model.lean), with the HOL notice in
[`Pancake/RiscV/COPYRIGHT`](Pancake/RiscV/COPYRIGHT).

Build it with:

```sh
lake build
```

The staged port is documented in [`PLAN.md`](PLAN.md).
