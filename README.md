This project is an ongoing port of the Pancake compiler to Lean. The CakeML
HOL development is included as the `cakeml` submodule; its Pancake sources are
in [`cakeml/pancake`](cakeml/pancake).

The Lean library currently contains the core Pancake syntax in
[`Pancake/Language.lean`](Pancake/Language.lean) and the first static-checker
data/context layer in [`Pancake/Static.lean`](Pancake/Static.lean), as well as
the Crepe IR and expression lowerer in [`Pancake/Crepe.lean`](Pancake/Crepe.lean)
and [`Pancake/PanToCrep.lean`](Pancake/PanToCrep.lean).

Build it with:

```sh
lake build
```

The staged port is documented in [`PLAN.md`](PLAN.md).
