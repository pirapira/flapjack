# Flapjack

Flapjack is beginning as a Lean 4 port of the formally verified Pancake
compiler. It is an early-stage project: the current Lean code covers the
front-end syntax and declaration-level checking foundations, the first Pancake-to-Crepe and
Crepe-to-Loop compiler slices, executable semantic fragments, and an initial
RISC-V model. The CakeML HOL development is included as the `cakeml`
submodule; its Pancake sources are in [`cakeml/pancake`](cakeml/pancake).

The Lean library currently contains the core Pancake syntax in
[`Flapjack/Language.lean`](Flapjack/Language.lean) and the static-checker
data/context layer plus shape-aware core expression and structured-program
checkers in [`Flapjack/Static.lean`](Flapjack/Static.lean), as well as
the Crepe IR and expression lowerer in [`Flapjack/Crepe.lean`](Flapjack/Crepe.lean)
and [`Flapjack/PanToCrep.lean`](Flapjack/PanToCrep.lean).
The first HOL `pan_simp` normalization pass is in
[`Flapjack/PanSimp.lean`](Flapjack/PanSimp.lean); the HOL notice for the
front-end port is in [`Flapjack/COPYRIGHT`](Flapjack/COPYRIGHT).
Named-structure elimination is in
[`Flapjack/PanStructs.lean`](Flapjack/PanStructs.lean).
The global heap-rewriting core is in
[`Flapjack/PanGlobals.lean`](Flapjack/PanGlobals.lean).
The composed pass pipeline is in
[`Flapjack/Pipeline.lean`](Flapjack/Pipeline.lean).
Core structured statement lowering and top-level function assembly are in
[`Flapjack/Compile.lean`](Flapjack/Compile.lean).
The first executable local/memory semantics and preservation lemmas are in
[`Flapjack/Semantics.lean`](Flapjack/Semantics.lean).
The Loop intermediate language and Crepe-to-Loop compiler are in
[`Flapjack/Loop.lean`](Flapjack/Loop.lean) and
[`Flapjack/CrepToLoop.lean`](Flapjack/CrepToLoop.lean). The compiler now
threads fresh temporaries through expression lowering and handles the main
memory, control-flow, call, exception, return, shared-memory, and FFI
equations; the earlier structural helper remains available for comparison.
The first Loop data-flow analyses are in
[`Flapjack/LoopAnalysis.lean`](Flapjack/LoopAnalysis.lean).
The initial Word IR and Loop-to-Word lowering are in
[`Flapjack/Word.lean`](Flapjack/Word.lean); its backend subdirectory carries
the HOL notice at [`Flapjack/Word/COPYRIGHT`](Flapjack/Word/COPYRIGHT).
The initial RISC-V target vocabulary, register/memory primitives, and
`ADD`/`ADDI` transition slice are in [`Flapjack/RiscV/Model.lean`](Flapjack/RiscV/Model.lean).
The first Word-to-RISC-V selector and its straight-line soundness theorem are
in [`Flapjack/RiscV/Backend.lean`](Flapjack/RiscV/Backend.lean), with the HOL
notice in [`Flapjack/RiscV/COPYRIGHT`](Flapjack/RiscV/COPYRIGHT).
The selector’s function artifact records both emitted instructions and return
registers for the supported straight-line fragment.

Build it with:

```sh
lake build
```

The staged port is documented in [`PLAN.md`](PLAN.md).
