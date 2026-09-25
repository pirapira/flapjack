# PanGlobals carrier review (flapjack-6nn)

Source comparison of the original Cake `pan_globalsScript.sml` definitions
with the definitions called by the executed global compiler in
`Flapjack/Pancake/PanGlobals.lean`. Constructor cases, filtering order, and
projected values agree for these two helpers. They are not exact HOL ports:
production `Decl α` contains production `Exp α` (`Const` stores `α`) and
production `Shape` (named identifiers are `String`), whereas HOL `decl` uses
word-valued `ExpHOL width` and `ShapeHOL` with `mlstring` names. The
`names_as_string` qualifier only addresses the identifier component and cannot
make these generic production carriers equal to HOL's. Direct parity tests
exercise the constructor/order behavior on production values, not a typed HOL
carrier conversion. Neither definition is tagged.

An exact-carrier replacement requires definitions over `DeclHOL width` and
`ShapeHOL`, direct HOL rows reproduced at that carrier, and a reviewed
connection to the executed path. Until then retain these definitions as
Flapjack-specific behavior and track the replacement in
`flapjack-6nn.3.1`.

## Comparison

| HOL (`pan_globalsScript.sml`) | Lean (`PanGlobals.lean`) | classification |
| --- | --- | --- |
| `fperm_name_def` (:184) | `globalRenameFunctionName` (:433) | carrier-only (name swap, no new bytes) |
| `fperm_def` (:191) | `globalRenameProg` (:470) | documented mismatch: production `Prog α` / `Exp α` uses `Const : α`; HOL `prog` / `exp` uses `Const : 'a word`, as well as mlstring identifiers |
| `fperm_decs_def` (:216) | `globalRenameDecls` (:504) | documented mismatch: production `Decl α` / `Prog α` / `Exp α` uses `Const : α`; HOL `decl` / `prog` / `exp` uses `Const : 'a word`, as well as mlstring identifiers |
| `resort_decls_def` (:179) | `globalResortDecls` (:864) | documented mismatch: generic `Decl α` / `Exp α` payload and `String`/`Shape` carriers differ from HOL `DeclHOL width` / word-valued `ExpHOL width` / `ShapeHOL` |
| `dec_shapes_def` (:228) | `globalDeclShapes` (:993) | documented mismatch: consumes generic `Decl α` and returns production `Shape` (`String` names), rather than HOL `DeclHOL width` and `ShapeHOL` |
| `fresh_name_def` (:55) | `freshNameHOL` (:279) | carrier-only in shape, but constructs new names (`++ "'"`), so the `flapjack-0up` boundary witness is required |
| `new_main_name_def` (:224) | `globalNewMainName` (:871) | documented mismatch: takes generic `Decl α` / `Exp α` (`Const : α`) rather than HOL word-valued declarations, despite only projecting names |
| `fresh_name_def` (:55) | `globalFreshName`/`globalFreshNameAux` (:154/:145) | **beyond carrier**: fuel-bounded search via `globalApostrophes`, not HOL's unbounded `strcat`/`strlen` recursion |
| `compile_exp_def` (:18) | `globalCompileExp` (:32) | **beyond carrier**: `lookupInfo` on an association list with `BEq String`, not HOL `FLOOKUP` on a finite map |
| `compile_def` (:69) | `globalCompileProg` (:304) | **beyond carrier**: inherits the `globalCompileExp` list-vs-finite-map mismatch |
| `compile_decs_def` (:160) | `globalCompileDecsThreaded` (:1383) | **beyond carrier**: inherits the `globalCompileProg`/`globalCompileExp` mismatch (context threading itself matches HOL) |
| `compile_exp_def` (:18) | `compileExpCake` (:1810) | carrier-only: canonical `FLOOKUP` over `FiniteMap String` (representation matches HOL; keys still `String`) |
| `compile_def` (:69) | `compileProgCake` (:1946) | carrier-only (canonical) |
| `compile_decs_def` (:160) | `compileDecsCake` (:2120) | carrier-only (canonical) |
| `compile_top_def` (:236) | `globalCompileTopCake` (:2744) | carrier-only (canonical); not the whole executed path on its own |

## Qualification boundary

The earlier proposal to retag this equality-only cluster with
`names_as_string` was incorrect wherever the executable declaration retains
generic values. `resort_decls_def`/`fperm_decs_def` range over production
`Decl α`, `fperm_def` ranges over `Prog α`, and their expression `Const`
payload is `α`, not HOL's `'a word`; `dec_shapes_def` also returns production
`Shape`, not `ShapeHOL`. `new_main_name_def` takes generic production
`Decl α` even though its body projects only function names. Equality-only or
projection-only behavior does not erase these input type differences.
`fperm_name_def` and `fresh_name_def` remain names-only qualified cases; the
other five definitions stay untagged until the exact-carrier replacement is
connected to production.

Do **not** retag the executed `globalCompileExp`/`globalCompileProg`/
`globalCompileDecsThreaded` on the strength of the qualifier alone: their
association-list lookup is a representation mismatch independent of the
identifier carrier. The canonical `compileExpCake`/`compileProgCake`/
`compileDecsCake` (finite-map lookup, carrier-only) are the intended tags, but
the executed path still goes through the list-based definitions; routing the
executed path to the canonical definitions is tracked by
`flapjack-pxn.18.5.2.20.2`. The exact `mlstring` carriers are tracked by
`flapjack-pxn.18.3.5.8`.
