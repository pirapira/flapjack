# PanGlobals identifier-carrier review (flapjack-6nn)

Read-only source comparison of the original Cake `pan_globalsScript.sml`
definitions with the production Lean declarations in
`Flapjack/Pancake/PanGlobals.lean`, classifying each declaration as

- **carrier-only**: the only remaining difference is the identifier carrier
  (HOL `funname`/`varname`/`stcname` = `mlstring` vs Lean `String`), so it is a
  candidate for the narrow `reviewed_names_as_string` qualifier once the
  qualifier tooling (`flapjack-an4`) lands; or
- **beyond carrier**: at least one further mismatch (recursion shape, map
  representation, ...), so the qualifier alone does not license a tag.

Prerequisites not yet met: qualifier tooling `flapjack-an4` and generated-name
byte-boundary witnesses `flapjack-0up`. Nothing here is tagged; no Lean source
is changed by this review.

## Comparison

| HOL (`pan_globalsScript.sml`) | Lean (`PanGlobals.lean`) | classification |
| --- | --- | --- |
| `fperm_name_def` (:184) | `globalRenameFunctionName` (:433) | carrier-only (name swap, no new bytes) |
| `fperm_def` (:191) | `globalRenameProg` (:470) | carrier-only |
| `fperm_decs_def` (:216) | `globalRenameDecls` (:504) | carrier-only |
| `resort_decls_def` (:179) | `globalResortDecls` (:810) | carrier-only (decl-kind filters, names ignored) |
| `dec_shapes_def` (:228) | `globalDeclShapes` (:842) | carrier-only (names ignored) |
| `fresh_name_def` (:55) | `freshNameHOL` (:279) | carrier-only in shape, but constructs new names (`++ "'"`), so the `flapjack-0up` boundary witness is required |
| `new_main_name_def` (:224) | `globalNewMainName` (:824) | carrier-only (delegates to `freshNameHOL`); needs the same boundary witness |
| `fresh_name_def` (:55) | `globalFreshName`/`globalFreshNameAux` (:154/:145) | **beyond carrier**: fuel-bounded search via `globalApostrophes`, not HOL's unbounded `strcat`/`strlen` recursion |
| `compile_exp_def` (:18) | `globalCompileExp` (:32) | **beyond carrier**: `lookupInfo` on an association list with `BEq String`, not HOL `FLOOKUP` on a finite map |
| `compile_def` (:69) | `globalCompileProg` (:304) | **beyond carrier**: inherits the `globalCompileExp` list-vs-finite-map mismatch |
| `compile_decs_def` (:160) | `globalCompileDecsThreaded` (:1383) | **beyond carrier**: inherits the `globalCompileProg`/`globalCompileExp` mismatch (context threading itself matches HOL) |
| `compile_exp_def` (:18) | `compileExpCake` (:1810) | carrier-only: canonical `FLOOKUP` over `FiniteMap String` (representation matches HOL; keys still `String`) |
| `compile_def` (:69) | `compileProgCake` (:1946) | carrier-only (canonical) |
| `compile_decs_def` (:160) | `compileDecsCake` (:2120) | carrier-only (canonical) |
| `compile_top_def` (:236) | `globalCompileTopCake` (:2744) | carrier-only (canonical); not the whole executed path on its own |

## Proposed first narrow retag

The smallest genuinely carrier-only slice is the **rename/shape cluster**
`fperm_name_def`, `fperm_def`, `fperm_decs_def`, `resort_decls_def`,
`dec_shapes_def`. These construct no new name bytes, need no FFI boundary
witness, and are currently documented as `FLAPJACK-SPECIFIC` only because of the
identifier carrier.

Then, once `flapjack-0up` provides the byte-rangedness witness, retag
`freshNameHOL` and `globalNewMainName`.

Do **not** retag the executed `globalCompileExp`/`globalCompileProg`/
`globalCompileDecsThreaded` on the strength of the qualifier alone: their
association-list lookup is a representation mismatch independent of the
identifier carrier. The canonical `compileExpCake`/`compileProgCake`/
`compileDecsCake` (finite-map lookup, carrier-only) are the intended tags, but
the executed path still goes through the list-based definitions; routing the
executed path to the canonical definitions is tracked by
`flapjack-pxn.18.5.2.20.2`. The exact `mlstring` carriers are tracked by
`flapjack-pxn.18.3.5.8`.
