# The Pancake parser port

A Lean 4 port of Pancake's own front end: `panLexer`, the `panPEG` grammar and
the `panPtreeConversion` parse-tree conversion, producing Flapjack AST values.
Reference sources are `cakeml/pancake/parser/`.

## Modules

| Module | Ports |
| --- | --- |
| `Lexer.lean` | `panLexerScript.sml` — tokens, keywords, comments, positions |
| `Basic.lean` | parser state and the combinators standing in for `peg`/`pegexec` |
| `Expressions.lean` | `panPEG` shape and expression rules, with `conv_Shape`/`conv_Exp` |
| `Statements.lean` | `panPEG` statement and block rules, with `conv_Prog`/`conv_NonRecStmt` |
| `Localise.lean` | `localise_exp`, `localise_prog`, `localise_topdecs` |
| `Parser.lean` | `parse_topdecs_to_ast` and `parse_to_ast` |

Entry points:

```lean
Flapjack.Parser.parseTopDecs (ofInt : Int → α) (source : String)
  : Except (List ParseError) (List (Decl α))

Flapjack.Parser.parseProgram (ofInt : Int → α) (source : String)
  : Except (List ParseError) (Prog α)
```

`ofInt` turns a source literal into the target word type; real callers pass
`BitVec.ofInt 64`, matching `panLang`'s `i2w`.

## No intermediate parse tree

Upstream runs a PEG over the tokens to build a parse tree and then converts
that tree to the AST. This port keeps the grammar and its ordered choices but
builds the AST directly: each `panPEG` nonterminal is one Lean function
carrying the corresponding `conv_*` behaviour, named after the rule, so
`EShiftNT` is `parseEShift` and the two can be read side by side.

The reason is that porting the parse tree would mean porting HOL's `peg` and
`pegexec` theories and the `parsetree` type with them, for an artefact nothing
downstream consumes — the acceptance criteria, and every caller, want source
to AST. If a parse tree is later wanted in its own right, the grammar
functions are where it would attach.

Two consequences worth knowing. Ordered choice is `<|>` over a backtracking
parser, and every optional or repeated piece brackets its operator *together
with* its operand, matching `try`/`rpt` applying to a whole `seql`; wrapping
only the operator would let `<a, b>` consume its closing `>` as a comparison
with no way back. And the expression chain from `ExpNT` to `EBaseNT` descends
sixteen levels without consuming a token, so the recursion is structural on a
fuel bound rather than on the token list. `parseFuel` seeds it at
`40 * tokens + 64`, far above what the grammar can use, and exhaustion reports
its own message so it can never be read as a syntax error.

## Deliberate divergences

Three, each a case where upstream looks like it has an oversight rather than
an intention. All three are covered by tests in `Flapjack/Test/Parser.lean`.

**`@top`.** `get_keyword` maps both `@base` and `@top` to `BaseK`, so `@top`
currently means `@base` and `TopK` is unreachable — even though the grammar
accepts `TopK` and `conv_Exp` sends it to `TopAddr`. Here `@top` maps to
`topK` and parses as `TopAddr`.

**`Load32` in `localise_exp`.** The pass has cases for `Load` and `LoadByte`
but not `Load32`, so it falls to the catch-all and `ld32 x` leaves `x` marked
`Global` even where `x` is local. Handled here.

**`Store32` in `localise_prog`.** Likewise no `Store32` case, so neither
operand of `st32` is localised. Handled here.

All three read as constructors added after the code around them was written.
They are worth reporting upstream.

## Upstream behaviour preserved

These are surprising but intended, and are kept:

- A `-` immediately before a digit is part of the literal, so `x-1` lexes as
  `x` and `-1` with no operator between, and does not parse. `x - 1` does.
- Symbolic tokens are read greedily, so `>>` is one shift token and a nested
  struct needs a space before its closing chevrons: `<1, <2, 3> >`.
- Pancake has no `Greater`, so `a > b` becomes `Less` with the operands
  swapped; likewise `<=`, `>+` and `<=+`.
- Every bare identifier is `Global` out of the grammar; only the localisation
  pass makes any of them `Local`.
- `return f()` is a tail call, not a return of a call: `RetK` comes from the
  word `return` and `CallNT` is tried before `ReturnNT`.
- `__add_with_carry__` is a primitive rather than a call, in both its
  statement and declaration forms.
- Position arithmetic is approximate: a newline resets the column to 0 rather
  than 1, a symbol group advances by `LENGTH n - 1`, and a single-character
  token reports the same start and stop so the next token inherits its column.
  Rows are reliable; the tests assert rows and not columns.

## Location annotations

`add_locs_annot` is ported, but off by default: upstream emits it
unconditionally, wrapping every statement in
`Seq (Annot "location" "(r:c r:c)") _`, which roughly doubles the tree and
makes every AST comparison awkward. Pass `locations := true` to either entry
point to get upstream's output.

```lean
parseTopDecs ofInt source (locations := true)
```

One subtlety is reproduced: the `{ ... }` statement form gets no annotation of
its own, because `conv_Prog` reaches it as a `ProgNT` node and folds it into a
`Seq` without calling `add_locs_annot`. Every other statement form arrives as
a leaf or a `conv_NonRecStmt` node and is annotated. Ranges come from the
tokens a rule consumed rather than from a parse-tree node's `locs`, and agree
with upstream to the extent its position arithmetic is itself exact (see the
caveat above).

## Not ported

**`collect_globals`.** Upstream defines it, but `localise_topdecs` starts from
an empty scope and never calls it.

**`RetCallNT`.** In the grammar but unreachable: `CallNT` is tried first and
matches everything `RetCallNT` would, and `conv_Prog` has no case for it.

## Test corpora

`Flapjack/Test/Parser.lean` holds the hand-written checks: the lexer,
expression precedence and folding, every statement and declaration form, the
localisation pass, the error cases, and the downstream checks below. It also
runs all 38 examples from `panConcreteExamplesScript.sml`.

`Flapjack/Test/ParserStaticExamples.lean` runs the 276 referenced examples
from `cakeml/pancake/static_checker/panStaticExamplesScript.sml`. That file
exists to exercise the static checker, but it asserts `check_parse_success` on
every example first -- its own comment is "All examples should parse" -- which
makes it by far the larger parser corpus, reaching combinations of shapes,
structs, exceptions, shared memory, calls and handlers the concrete-syntax
examples do not. Only parsing is asserted there.

## Downstream compatibility

Parser output is fed into what already exists: `staticCheck` from
`Flapjack/Static.lean` and `compileToCrepe` from `Flapjack/Compile.lean`.
Those checks live in `Flapjack/Test/Parser.lean`.

Running Flapjack's `staticCheck` over all 273 static-checker examples that
carry an upstream verdict, **266 agree (97.4%)** and 7 disagree. All 7 were
checked by hand and none is a parsing problem -- the parser builds the
expected AST in each case:

| Example | Upstream | Flapjack |
| --- | --- | --- |
| `ex_redefined_var_dec_deccall` | accepts | rejects |
| `ex_redefined_var_deccall_deccall` | accepts | rejects |
| `ex_redefined_global_var` | accepts | rejects |
| `ex_redefined_global_var_deccall` | accepts | rejects |
| `ex_struct_field_reordered` | accepts | rejects |
| `ex_shared_ldw_rstruct_dest` | rejects | accepts |
| `ex_shared_ldw_nstruct_dest` | rejects | accepts |

The first five are redefinition and field-ordering policy: upstream permits
what `Flapjack/Static.lean` refuses. The last two are a shape check upstream
performs and Flapjack does not -- `!ldw x, 0` where `x` has a struct shape
parses correctly and is caught by neither the grammar nor Flapjack's checker.
These are `Flapjack/Static.lean` gaps rather than parser gaps, and are left
alone here; they are listed so they are not lost.

## Diagnostics

Lexical errors are collected and reported together, as `safe_pancake_lex`
does. A parse error is reported singly, taken from the alternative that
consumed the most input — with ordered choice the last alternative tried is
usually the least relevant, so the deepest failure is the one to show.
`formatError` renders `row:col: message`.
