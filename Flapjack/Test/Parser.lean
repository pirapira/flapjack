import Flapjack.Parser
import Flapjack.Static
import Flapjack.Compile

/-!
Parser tests.

Checks fall into three groups: the lexer against representative Pancake
snippets, the grammar against expected ASTs, and every example from
`cakeml/pancake/parser/panConcreteExamplesScript.sml` for acceptance and
rejection.

Assertions are `#guard`, which evaluates at compile time and fails the build,
so the suite runs as part of `lake build` and needs no axiom. AST equality
goes through the derived `Repr`: it prints every constructor and field, so two
distinct trees never render alike, and unlike `rfl` it does not ask the kernel
to reduce the parser -- which takes minutes even for one small program.
-/

namespace Flapjack.Test.Parser

open Flapjack Flapjack.Parser

/-- The tests parse into `Int` constants; real users pass `BitVec.ofInt 64`. -/
abbrev ofI : Int → Int := fun value => value

/-- Compare two ASTs through their derived `Repr`. -/
def sameAst {α : Type} [Repr α] (actual expected : α) : Bool :=
  reprStr actual == reprStr expected

def accepts (source : String) : Bool :=
  (parseTopDecs ofI source).toOption.isSome

def rejects (source : String) : Bool :=
  (parseTopDecs ofI source).toOption.isNone

/-- Parse a statement sequence, for the expression and statement tests. -/
def prog (source : String) : Except (List ParseError) (Prog Int) :=
  parseProgram ofI source

/-- Parse a bare expression by wrapping it in a `return`. -/
def expr (source : String) : Except (List ParseError) (Prog Int) :=
  parseProgram ofI s!"return {source};"

/-! ### Lexer -/

#guard (pancakeLex "x + 1").map (·.1) == [.identT "x", .plusT, .intT 1]

-- `//` runs to end of line; the block forms are `/* */` and `/@ @/`.
#guard (pancakeLex "1 // two\n3").map (·.1) == [.intT 1, .intT 3]
#guard (pancakeLex "1 /* two */ 3").map (·.1) == [.intT 1, .intT 3]
#guard (pancakeLex "/@ note @/").map (·.1) == [.annotCommentT " note "]

-- A `-` directly before a digit is part of the literal, so `x-1` is two tokens
-- with no operator between them. This is upstream behaviour.
#guard (pancakeLex "-3").map (·.1) == [.intT (-3)]
#guard (pancakeLex "x-1").map (·.1) == [.identT "x", .intT (-1)]
#guard (pancakeLex "x - 1").map (·.1) == [.identT "x", .minusT, .intT 1]

-- Symbolic tokens are read greedily, so `>>` is one shift token. That is why a
-- nested struct needs a space before its closing chevrons.
#guard (pancakeLex ">>").map (·.1) == [.asrT]
#guard (pancakeLex ">>>").map (·.1) == [.lsrT]
#guard (pancakeLex "#>>").map (·.1) == [.rorT]
#guard (pancakeLex ">=+").map (·.1) == [.higheqT]

-- `@base`, `@biw` and `@top` are keywords; any other `@name` is a foreign
-- identifier with the `@` stripped.
#guard (pancakeLex "@base @biw @top @write").map (·.1)
  == [.keywordT .baseK, .keywordT .biwK, .keywordT .topK, .foreignIdent "write"]

-- Rows advance across lines. Columns follow `panLexer`'s arithmetic, which is
-- approximate by design: a newline resets the column to 0, and a single-
-- character token reports the same start and stop, so the next token inherits
-- that column. Only rows are asserted here.
#guard (pancakeLex "1\n2\n3").map (fun entry =>
    match entry.2.start with
    | .posn row _ => row
    | _ => 0)
  == [1, 2, 3]

-- An unrecognised character is a lexical error rather than a silent skip.
#guard rejects "fun f() { return `; }"

/-! ### Expressions -/

-- A run of one associative operator flattens into a single `Op`.
#guard sameAst (expr "a + b + c")
  (.ok (.return (.op .add [.var .global "a", .var .global "b", .var .global "c"])))

-- Subtraction is binary, so it nests instead of flattening.
#guard sameAst (expr "a - b - c")
  (.ok (.return (.op .sub [.op .sub [.var .global "a", .var .global "b"], .var .global "c"])))

-- Multiplication binds tighter than addition and nests to the left.
#guard sameAst (expr "1 + 2 * 3 - 4")
  (.ok (.return (.op .sub
    [.op .add [.const 1, .panOp .mul [.const 2, .const 3]], .const 4])))

-- Pancake has no `Greater`, so `a > b` is `Less` with the operands swapped.
#guard sameAst (expr "a > b") (.ok (.return (.cmp .less (.var .global "b") (.var .global "a"))))
#guard sameAst (expr "a < b") (.ok (.return (.cmp .less (.var .global "a") (.var .global "b"))))
#guard sameAst (expr "a >= b") (.ok (.return (.cmp .notLess (.var .global "a") (.var .global "b"))))
#guard sameAst (expr "a <= b") (.ok (.return (.cmp .notLess (.var .global "b") (.var .global "a"))))
#guard sameAst (expr "a <+ b") (.ok (.return (.cmp .lower (.var .global "a") (.var .global "b"))))
#guard sameAst (expr "a >+ b") (.ok (.return (.cmp .lower (.var .global "b") (.var .global "a"))))

-- `!e` is `e == 0`, and `&&`/`||` compare each operand against zero.
#guard sameAst (expr "!a") (.ok (.return (.cmp .equal (.const 0) (.var .global "a"))))
#guard sameAst (expr "a && b")
  (.ok (.return (.op .and
    [.cmp .notEqual (.const 0) (.var .global "a"),
     .cmp .notEqual (.const 0) (.var .global "b")])))
#guard sameAst (expr "a || b")
  (.ok (.return (.cmp .notEqual (.const 0)
    (.op .or [.var .global "a", .var .global "b"]))))

-- `true` and `false` are the constants 1 and 0.
#guard sameAst (expr "true") (.ok (.return (.const 1)))
#guard sameAst (expr "false") (.ok (.return (.const 0)))

-- Field access chains left, positionally or by name.
#guard sameAst (expr "x.0.name")
  (.ok (.return (.nField "name" (.rField 0 (.var .global "x")))))

-- A shape literal `n` means `n` copies of `One`.
#guard sameAst (expr "lds 2 x")
  (.ok (.return (.load (.comb [.one, .one]) (.var .global "x"))))
#guard sameAst (expr "lds {1,{1,1}} x")
  (.ok (.return (.load (.comb [.one, .comb [.one, .one]]) (.var .global "x"))))
#guard sameAst (expr "ld8 x") (.ok (.return (.loadByte (.var .global "x"))))
#guard sameAst (expr "ld32 x") (.ok (.return (.load32 (.var .global "x"))))

-- Structs, raw and named. The space before the final `>` is needed because
-- `>>` lexes as one token.
#guard sameAst (expr "<a, b>")
  (.ok (.return (.rStruct [.var .global "a", .var .global "b"])))
#guard sameAst (expr "<1, <2, 3> >")
  (.ok (.return (.rStruct [.const 1, .rStruct [.const 2, .const 3]])))
#guard sameAst (expr "pt<x = 1, y = 2>")
  (.ok (.return (.nStruct "pt" [("x", .const 1), ("y", .const 2)])))

#guard sameAst (expr "@base") (.ok (.return .baseAddr))
#guard sameAst (expr "@biw") (.ok (.return .bytesInWord))

-- `@top` is `TopAddr`. Upstream's lexer maps `@top` to the `@base` keyword,
-- which looks like a slip: the grammar and the conversion both handle `TopK`.
#guard sameAst (expr "@top") (.ok (.return .topAddr))

-- Shift operators.
#guard sameAst (expr "a << 2") (.ok (.return (.shift .lsl (.var .global "a") (.const 2))))
#guard sameAst (expr "a >>> 2") (.ok (.return (.shift .lsr (.var .global "a") (.const 2))))
#guard sameAst (expr "a >> 2") (.ok (.return (.shift .asr (.var .global "a") (.const 2))))
#guard sameAst (expr "a #>> 2") (.ok (.return (.shift .ror (.var .global "a") (.const 2))))

-- A shape must be positive.
#guard rejects "fun f() { return lds 0 1; }"

/-! ### Statements -/

#guard sameAst (prog "skip;") (.ok .skip)
#guard sameAst (prog "break;") (.ok .break)
#guard sameAst (prog "continue;") (.ok .continue)
#guard sameAst (prog "tick;") (.ok .tick)

#guard sameAst (prog "x = 1;") (.ok (.assign .global "x" (.const 1)))
#guard sameAst (prog "st 1, 2;") (.ok (.store (.const 1) (.const 2)))
#guard sameAst (prog "st8 1, 2;") (.ok (.storeByte (.const 1) (.const 2)))
#guard sameAst (prog "st32 1, 2;") (.ok (.store32 (.const 1) (.const 2)))

-- Shared memory: `!ldw` and friends load, `!stw` and friends store.
#guard sameAst (prog "!ldw v, 8;") (.ok (.shMemLoad .opW .global "v" (.const 8)))
#guard sameAst (prog "!ld8 v, 8;") (.ok (.shMemLoad .op8 .global "v" (.const 8)))
#guard sameAst (prog "!ld16 v, 8;") (.ok (.shMemLoad .op16 .global "v" (.const 8)))
#guard sameAst (prog "!ld32 v, 8;") (.ok (.shMemLoad .op32 .global "v" (.const 8)))
#guard sameAst (prog "!stw 8, 1;") (.ok (.shMemStore .opW (.const 8) (.const 1)))
#guard sameAst (prog "!st8 8, 1;") (.ok (.shMemStore .op8 (.const 8) (.const 1)))
#guard sameAst (prog "!st16 8, 1;") (.ok (.shMemStore .op16 (.const 8) (.const 1)))
#guard sameAst (prog "!st32 8, 1;") (.ok (.shMemStore .op32 (.const 8) (.const 1)))

#guard sameAst (prog "@write(1, 2, 3, 4);")
  (.ok (.extCall "write" (.const 1) (.const 2) (.const 3) (.const 4)))

#guard sameAst (prog "throw E 1;") (.ok (.raise "E" (.const 1)))
#guard sameAst (prog "return 1;") (.ok (.return (.const 1)))

-- Statements sequence to the right, and the last one carries no trailing
-- `Skip`.
#guard sameAst (prog "skip; tick;") (.ok (.seq .skip .tick))

-- A declaration scopes over everything after it.
#guard sameAst (prog "var x = 1; return x;")
  (.ok (.dec "x" .one (.const 1) (.return (.var .local "x"))))

-- An empty body is `Skip`; a missing `else` is `Skip`.
#guard sameAst (prog "if 1 { }") (.ok (.ite (.const 1) .skip .skip))
#guard sameAst (prog "if 1 { tick; } else { skip; }")
  (.ok (.ite (.const 1) .tick .skip))
#guard sameAst (prog "while 1 { tick; }") (.ok (.while (.const 1) .tick))

-- The three call forms. `return f()` is the tail call: the `RetK` token comes
-- from the word `return`, and `CallNT` is tried before `ReturnNT`, so
-- `return f()` is a call and `return 1` a return.
#guard sameAst (prog "return f();") (.ok (.call none "f" []))
#guard sameAst (prog "f();") (.ok (.call (some (none, none)) "f" []))
#guard sameAst (prog "x = f(1);")
  (.ok (.call (some (some (.global, "x"), none)) "f" [.const 1]))

-- A handler binds its exception variable over the handler body.
#guard sameAst (prog "try y = f() catch E => e { y = e; }")
  (.ok (.call (some (some (.global, "y"), some ("E", "e", .assign .global "y" (.var .local "e"))))
    "f" []))

-- `var x = f(args);` is a `DecCall`, distinct from a declaration whose value
-- happens to be a variable.
#guard sameAst (prog "var x = f(1); return x;")
  (.ok (.decCall "x" .one "f" [.const 1] (.return (.var .local "x"))))
#guard sameAst (prog "var x = f; return x;")
  (.ok (.dec "x" .one (.var .global "f") (.return (.var .local "x"))))

-- An annotation comment becomes an `Annot` statement tagged `@`.
#guard sameAst (prog "/@ hello @/ skip;") (.ok (.seq (.annot "@" " hello ") .skip))

/-! ### `__add_with_carry__` -/

-- As a call it becomes a primitive, taking its result variable from the
-- assignment target.
#guard sameAst (prog "r = __add_with_carry__(a, b, c);")
  (.ok (.primitive "r" .addCarry [.var .global "a", .var .global "b", .var .global "c"]))

-- As a declaration it becomes a declaration of the shape's zero value followed
-- by the primitive.
#guard sameAst (prog "var {1,1} r = __add_with_carry__(a, b, c); return r;")
  (.ok (.dec "r" (.comb [.one, .one]) (.rStruct [.const 0, .const 0])
    (.seq (.primitive "r" .addCarry [.var .global "a", .var .global "b", .var .global "c"])
      (.return (.var .local "r")))))

-- With no variable to bind, there is nothing for the primitive to write to, so
-- it is rejected rather than silently dropped.
#guard rejects "fun f() { __add_with_carry__(a, b, c); }"

/-! ### Declarations -/

#guard sameAst (parseTopDecs ofI "var 1 x = 1;") (.ok [.decl .one "x" (.const 1)])
#guard sameAst (parseTopDecs ofI "exception E : 1;") (.ok [.exnDecl "E" .one])
#guard sameAst (parseTopDecs ofI "struct pt { 1 x, 1 y }")
  (.ok [.name "pt" [("x", .one), ("y", .one)]])

-- A function's shape sits before its name; `inline` and `export` precede `fun`,
-- and both default to false.
#guard sameAst (parseTopDecs ofI "fun 1 f(1 a) { return a; }")
  (.ok [.function { name := "f", inline := false, exported := false,
                    params := [("a", .one)], body := .return (.var .local "a"),
                    returnShape := .one }])
#guard sameAst (parseTopDecs ofI "inline export fun f() { skip; }")
  (.ok [.function { name := "f", inline := true, exported := true,
                    params := [], body := .skip, returnShape := .one }])

/-! ### Localisation

The grammar cannot tell a local from a global, so every variable starts
`Global` and this pass reclassifies the bound ones. -/

-- A parameter is local; an undeclared name stays global.
#guard sameAst (parseTopDecs ofI "fun f(1 a) { return a + b; }")
  (.ok [.function { name := "f", inline := false, exported := false,
                    params := [("a", .one)],
                    body := .return (.op .add [.var .local "a", .var .global "b"]),
                    returnShape := .one }])

-- A declaration shadows a global from its own scope onwards, but not before:
-- the assignment to `x` targets the global, and the `return` the local.
#guard sameAst (parseTopDecs ofI "var 1 x = 0; fun f() { x = 1; var 1 x = 5; return x; }")
  (.ok [.decl .one "x" (.const 0),
        .function { name := "f", inline := false, exported := false, params := [],
                    body := .seq (.assign .global "x" (.const 1))
                      (.dec "x" .one (.const 5) (.return (.var .local "x"))),
                    returnShape := .one }])

-- A handler's exception variable is local inside the handler only.
#guard sameAst (parseTopDecs ofI "fun f() { try g() catch E => e { x = e; } return e; }")
  (.ok [.function { name := "f", inline := false, exported := false, params := [],
                    body := .seq
                      (.call (some (none, some ("E", "e", .assign .global "x" (.var .local "e"))))
                        "g" [])
                      (.return (.var .global "e")),
                    returnShape := .one }])

-- `ld32` and `st32` are localised. Upstream's `localise_exp` has no `Load32`
-- case and its `localise_prog` no `Store32` case, so both leave their operands
-- marked `Global`; those look like constructors added after the pass was
-- written.
#guard sameAst (prog "var v = 1; return ld32 v;")
  (.ok (.dec "v" .one (.const 1) (.return (.load32 (.var .local "v")))))
#guard sameAst (prog "var v = 1; st32 v, v;")
  (.ok (.dec "v" .one (.const 1) (.store32 (.var .local "v") (.var .local "v"))))

/-! ### Errors

Invalid syntax gives a structured error with a position, not a silent
fallback. -/

-- A missing semicolon says so, and names the line it is missing from. The
-- column is not asserted: position arithmetic is ported as-is from
-- `panLexer`, including its quirks (a symbol group advances by
-- `LENGTH n - 1`, and a newline resets the column to 0 rather than 1), so
-- pinning exact columns here would fix numbers this port did not choose.
#guard match parseTopDecs ofI "fun f() { skip }" with
  | .error [error] =>
      error.message == "Failed to see expected token: ;"
        && (match error.locs.start with
            | .posn row _ => row == 1
            | _ => false)
  | _ => false

-- The error is reported at the offending token rather than at the end of the
-- statement before it, so a `}` on line 4 standing where a `;` was expected is
-- reported on line 4.
#guard match parseTopDecs ofI "fun f() {\n  skip;\n  skip\n}" with
  | .error [error] =>
      match error.locs.start with
      | .posn row _ => row == 4
      | _ => false
  | _ => false

-- The reported error comes from the alternative that got furthest, so a
-- truncated program still yields exactly one error.
#guard match parseTopDecs ofI "fun f() {" with
  | .error [_] => true
  | _ => false

-- Lexical errors are reported together, and before parsing.
#guard match parseTopDecs ofI "fun f() { return `; } fun g() { return ~; }" with
  | .error errors => errors.length == 2
  | _ => false

#guard rejects "fun f() { skip }"
#guard rejects "fun f() { "
#guard rejects "fun f( { skip; }"
#guard rejects "f() { skip; }"
#guard rejects "fun f() { if 1 skip; }"
#guard rejects "var x = ;"
#guard rejects "exception E 1;"
#guard rejects "struct pt 1 x }"

-- An unterminated block comment is a lexical error.
#guard rejects "fun f() { /* unterminated\n return 1; }"

/-! ### Word-typed constants

The tests above parse into `Int`; this is the shape real callers use. -/

#guard sameAst (parseTopDecs (BitVec.ofInt 64) "fun f() { return 42; }")
  (.ok [.function { name := "f", inline := false, exported := false, params := [],
                    body := .return (.const (BitVec.ofInt 64 42)), returnShape := .one }])

/-! ### Location annotations

`add_locs_annot` is off by default and reproduces upstream's output when asked
for. -/

-- Off by default.
#guard sameAst (prog "skip; tick;") (.ok (.seq .skip .tick))

-- On, each statement is wrapped in its own source range.
#guard sameAst (parseProgram ofI "skip; tick;" (locations := true))
  (.ok (.seq
    (.seq (.annot "location" "(1:1 1:5)") .skip)
    (.seq (.annot "location" "(1:6 1:10)") .tick)))

-- A declaration's range covers the statements it scopes over.
#guard sameAst (parseProgram ofI "var x = 1; return x;" (locations := true))
  (.ok (.seq (.annot "location" "(1:1 1:18)")
    (.dec "x" .one (.const 1)
      (.seq (.annot "location" "(1:10 1:18)") (.return (.var .local "x"))))))

-- Ranges track rows through a multi-line function.
#guard sameAst (parseTopDecs ofI "fun f() {\n  skip;\n  tick;\n}" (locations := true))
  (.ok [.function { name := "f", inline := false, exported := false, params := [],
                    body := .seq
                      (.seq (.annot "location" "(2:2 2:6)") .skip)
                      (.seq (.annot "location" "(3:2 3:6)") .tick),
                    returnShape := .one }])

-- An `if` is annotated, and so is the statement inside it. The implicit
-- `else` is annotated too, with `UNKNOWN`: upstream's `try_default` supplies a
-- `SkipK` leaf carrying `unknown_loc`, and `conv_Prog` annotates every leaf it
-- converts, so `(UNKNOWN UNKNOWN)` is upstream's own output here.
#guard sameAst (parseProgram ofI "if 1 { skip; }" (locations := true))
  (.ok (.seq (.annot "location" "(1:1 1:12)")
    (.ite (.const 1)
      (.seq (.annot "location" "(1:7 1:11)") .skip)
      (.seq (.annot "location" "(UNKNOWN UNKNOWN)") .skip))))

-- The `{ ... }` statement form gets no annotation of its own: `conv_Prog`
-- reaches it as a `ProgNT` node and folds it without calling
-- `add_locs_annot`. Only the statement inside is annotated.
#guard sameAst (parseProgram ofI "{ skip; };" (locations := true))
  (.ok (.seq (.annot "location" "(1:2 1:6)") .skip))

/-! ### The parse tree

The grammar and the conversion are separate stages, so the tree is worth
checking directly: `conv_*` matches on how many children a node has, which
makes the `consume` / `keep` split part of the grammar's contract. -/

/-- Render a tree as `(nonterminal child ...)`, for comparing shapes. -/
def treeShape : ParseTree → String
  | .lf token _ => (reprStr token).replace "Flapjack.Parser.Token." ""
  | .nd nonterminal children _ =>
      "(" ++ (reprStr nonterminal).replace "Flapjack.Parser.Nonterminal." "" ++
        String.join (children.map (fun child => " " ++ treeShape child)) ++ ")"

def treeOf (source : String) : Option String :=
  let toks := pancakeLex source
  match (gTopDecList (parseFuel toks.length) (PState.ofToks toks)).1 with
  | some [tree] => some (treeShape tree)
  | _ => none

-- `PState.remaining` mirrors `toks.length` so that spans and fuel do not have
-- to walk the remaining tokens (#405). Nothing reports it drifting: a rule
-- that consumed a token without going through `PState.pop` would just compute
-- short spans. So check the invariant directly, on input that exercises every
-- consuming primitive -- keywords, identifiers, integers, and punctuation.
def remainingTracksToks (source : String) : Bool :=
  let toks := pancakeLex source
  let final := (gTopDecList (parseFuel toks.length) (PState.ofToks toks)).2
  final.remaining == final.toks.length

#guard remainingTracksToks "var 1 x = 1;"
#guard remainingTracksToks "exception E : 1;"
#guard remainingTracksToks "fun f(1 a, 1 b) { var x = a + b * 2; return x; }"
#guard remainingTracksToks "fun g() { if 1 < 2 { skip; } else { skip; } while 1 { skip; } }"
#guard remainingTracksToks "fun h() { var y = <1, 2>; st 8, y.0; return 0; }"
#guard remainingTracksToks "fun k() { var r = @foo(1, 2, 3, 4); raise E 1; }"

-- The invariant has to survive backtracking, which is where a rewind that
-- restored `toks` but not `remaining` would show up: `<a, b>` commits to a
-- comparison, fails on the closing `>`, and unwinds to parse a struct.
#guard remainingTracksToks "fun b() { var s = <1, 2>; var c = 1 < 2; return 0; }"

-- `TopDecListNT` nests as `[item, rest]` and ends with an empty node, which is
-- what `conv_TopDecList` matches.
#guard treeOf "exception E : 1;"
  == some "(topDecList (exnDec identT \"E\" intT 1) (topDecList))"

-- `GlobalDecNT` has three children because `ShapedIdentNT` contributes a shape
-- and a name rather than a node of its own.
#guard treeOf "var 1 x = 1;" == some
  "(topDecList (globalDec intT 1 identT \"x\" (exp (eBoolAnd (eEq (eCmp (eOr (eXor (eAnd (eShift (eAdd (eMul (eNot (eField intT 1))))))))))))) (topDecList))"

-- An omitted shape becomes a `DefaultShT` leaf, so the child count is stable.
#guard treeOf "var x = 1;" == some
  "(topDecList (globalDec defaultShT identT \"x\" (exp (eBoolAnd (eEq (eCmp (eOr (eXor (eAnd (eShift (eAdd (eMul (eNot (eField intT 1))))))))))))) (topDecList))"

-- `FunNT` has exactly six children -- inline, export, shape, name, params,
-- body -- with `NoinlineT` and `StaticT` leaves standing in for the absent
-- modifiers, which is what `conv_TopDec` matches on.
#guard treeOf "fun f() { skip; }" == some
  "(topDecList (funNT noinlineT staticT defaultShT identT \"f\" (paramList) (prog keywordT (Flapjack.Parser.Keyword.skipK))) (topDecList))"

-- `consume` contributes no child: the `lds` keyword and the shape braces are
-- absent from the tree, leaving just shape and address.
#guard treeOf "fun f() { return lds 2 x; }" == some
  "(topDecList (funNT noinlineT staticT defaultShT identT \"f\" (paramList) (prog (returnNT (exp (eBoolAnd (eEq (eCmp (eLoad intT 2 (eOr (eXor (eAnd (eShift (eAdd (eMul (eNot (eField identT \"x\")))))))))))))))) (topDecList))"

-- A tree the grammar cannot produce converts to `none` rather than being
-- repaired: `conv_Shape` refuses a non-positive literal.
#guard (convShape 64 (.lf (.intT 0) unknownLoc)).isNone

-- And `conv_binop` refuses a token that is not one.
#guard (convBinop (.lf (.starT) unknownLoc) == (none : Option BinOp))

/-! ### Downstream compatibility

The AST the parser produces has to be consumable by what already exists, not
merely well-formed. These feed parser output straight into Flapjack's static
checker and its Pancake-to-Crepe compiler. -/

-- Flapjack's own static checker accepts a valid parsed program.
#guard match parseTopDecs ofI "fun 1 main() { return 1; }" with
  | .ok declarations => staticResultOk (staticCheck declarations)
  | .error _ => false

-- And rejects one upstream also rejects: `main` may not take parameters. This
-- is `ex_arg_main` from the static-checker examples.
#guard match parseTopDecs ofI "fun 1 main (1 a) {\n  return 1;\n}" with
  | .ok declarations => !staticResultOk (staticCheck declarations)
  | .error _ => false

-- Parsed declarations compile through `compileToCrepe`, producing one
-- compiled function per source function.
#guard match parseTopDecs (BitVec.ofInt 64)
    "fun 1 f(1 a) { return a + 1; }\nfun 1 main() { var 1 r = f(2); return r; }" with
  | .ok declarations =>
      (compileToCrepe
        { vars := [], functions := [], exceptions := [], maxVar := 0,
          bytesInWord := BitVec.ofNat 64 8 } declarations).length == 2
  | .error _ => false

/-! ### Every example from `panConcreteExamplesScript.sml`

Upstream marks each of these `check_success` or `check_failure`. The two it
leaves unchecked (`ex4'`, `struct_arguments`) are valid programs and are
required to parse here. -/

-- ex1
#guard accepts "\n  fun cond() {\n    if 2 >= 1 { x = 2; }\n  }"
-- ex2
#guard accepts "\n  fun main() {\n    if !b & (a ^ c) & d {\n      return foo(1, <2, 3>);\n        } else {\n      return goo(4, 5, 6);\n    }\n  }"
-- ex2_and_a_half
#guard accepts "\n  fun main() {\n    return(a && b && c || a || b ^ d);\n  }"
-- ex3
#guard accepts "\n  fun boolfun() {\n    if b & (a ^ c) & d { return true; }\n    else { return false; }\n  }"
-- ex3_and_a_half
#guard accepts "\n  fun cmps () {\n    var x = 2;\n    var y = 3;\n    var z = (x & y != 0);\n    z = ((x & y) != 0);\n    z = (y & x != 0);\n    z = ((y & x) != 0);\n}"
-- ex4
#guard accepts "\n  fun loopy() {\n    while b | c {\n      if x >= 5 {\n        break;\n      } else {\n        st8 y, 8; // store byte\n        @foo(x,y,k,z); // ffi function call with pointer args\n        x = x + 1;\n        y = x + 1;\n      }\n    }\n  }"
-- ex4'
#guard accepts "\n  fun loopy() {\n    while b | c {\n      if x >= 5 {\n        break;\n      } else {\n        st32 y, 8; // store byte\n        @foo(x,y,k,z); // ffi function call with pointer args\n        x = x + 1;\n        y = x + 1;\n      }\n    }\n  }"
-- ex5
#guard accepts "\n  fun foo () {\n    var b = 5;\n    b = b + 1;\n    if b >= 5 {\n      throw Err 5;\n    }\n  }"
-- ex6
#guard accepts "\n  fun foo () {\n    {var b = 5;\n     b = b + 1;};\n     if b >= 5 {\n       throw Err 5;\n     }\n  }"
-- ex7
#guard accepts "\n  fun loader() {\n    x = lds {1,1,2} y;\n  }"
-- ex7_and_a_half
#guard accepts "\n  fun loader() {\n    x = lds {3,1,{1,{2,1}}} y;\n  }"
-- ex7_and_three_quarters
#guard accepts "\n  fun loader() {\n    x = lds {1,{1}} y;\n  }"
-- ex8
#guard accepts "\n  fun cmps () {\n    x = a < b;\n    x = b > a;\n    x = b >= a;\n    x = a <= b;\n    x = a != b;\n    x = a <+ b;\n    x = b >+ a;\n    x = b >=+ a;\n    x = a <=+ b;\n  }"
-- ex8_and_a_half
#guard accepts "\n  fun mul() {\n    x = a * b;\n    x = a * b * c;\n    x =  (a + b) * c;\n    x = a + b * c;\n    x = a * b + c;\n   }"
-- ex9
#guard accepts "\n fun testfun() {\n   var a = @base;\n   var b = 8;\n   var c = @base + 16;\n   var d = 1;\n   @out_morefun(a,b,c,d);\n   st @base, ic;\n   return @top;\n }"
-- ex10
#guard accepts "\n fun testfun() {\n   var a = 1 << 2;\n   a = a >>> 1 + 1;\n   a = a << a #>> 2 >> 3;\n   return 1;\n }"
-- argument_call
#guard accepts "\n  fun main() {\n    var x = 0;\n    var r = 0;\n    r = g(x);\n    return r;\n  }\n\n  fun g(1 v, 1 u) {\n    return v + u + 1;\n  }"
-- ret_call
#guard accepts "\n  fun main() {\n    var r = 0;\n    r = g(); // This is an assigning call (but could be optimised to a tail call)\n    return r;\n  }\n\n  fun f() {\n    var 1 r = g(); // Function calls can be used to initialise variables,\n                   // but the expected shape of the return value must be declared\n    return r;\n  }\n\n  fun g() {\n    g(); // This is a stand-alone call\n    return g(); // This is a tail call\n  }"
-- struct_access
#guard accepts "\n  fun g() {\n    var v = < 0, 1, 2 >;\n    var w = < 9, 9 >.2;\n\n    return v.1;\n  }"
-- struct_arguments
#guard accepts "\n  fun g() {\n    var v = < 0, 1, < 2, 3, 4 > >;\n    var r = 0;\n    r = f(v);\n    r = l(v);\n\n    var w = < 9, 9 >;\n    r = h(w);\n\n    var u = < < 1, 2>,\n              1,\n              < < 3, 4 > >\n            >;\n    r = k(u);\n\n\n    return 0;\n  }\n\n  fun f({1,1,3} x) {\n    return x.2.1;\n  }\n\n  fun l({1,1,{1,1,1}} x) {\n    return x.2.1;\n  }\n\n  fun k({2,1,{2}} x) {\n    return x.2.0.0;\n  }\n\n  fun h(2 x) {\n    return x.0;\n  }"
-- locmem_ex
#guard accepts "\n  fun test_locmem() {\n    var v = 12;\n    st 1000, 1 + 1; // store 1 + 1 (ie 2) at local memory address 1000\n    st8 1000 + 4, v; // store byte from variable v (12) to local memory address 1004\n    st32 1000 + 4, v; // store word32 from variable v (12) to local memory address 1004\n    v = lds 1 1000 + 8; // load word from local address 1008 and assign to variable v\n    v = ld8 1000 + 4 * 3; // load byte from local address 1012 and assign to variable v\n    v = ld32 1000 + 4 * 3; // load word32 from local address 1012 and assign to variable v\n  }"
-- shmem_ex
#guard accepts "\n  fun test_shmem() {\n    var v = 12;\n    !st8 1000, v; // store byte from variable v (12) to shared memory address 1000\n    !st16 1000, v; // store 32 bits from variable v (12) to shared memory address 1000\n    !st32 1000, v; // store 32 bits from variable v (12) to shared memory address 1000\n    !stw 1004, 1+1; // store 1+1 (aka 2) to shared memory address 1004\n    !ld8 v, 1000 + 12; // load byte stored in shared memory address 1012 to v\n    !ld16 v, 1000 + 12; // load 32 bits from shared memory address 1012 to v\n    !ld32 v, 1000 + 12; // load 32 bits from shared memory address 1012 to v\n    !ldw v, 1000 + 12 * 2; // load word stored in shared memory address 1024 to v\n  }"
-- comment_ex
#guard accepts "/* this /* non-recursive block comment\n   */\n  // and these single-line comments\n  fun main() { //should not interfer with parsing\n    return /* nor shoud this */ 1;\n  }\n "
-- entry_fun
#guard accepts "\n  export fun f() {\n    // this function can be called externally\n    return 1;\n  }\n\n  fun g() {\n    // this function cannot\n    return 2;\n  }\n "
-- empty_body
#guard accepts "\n  fun f() {}\n\n  fun g(1 x) {}\n  "
-- empty_blocks
#guard accepts "\n  fun f() { while(1) {} }\n\n  fun g() { if(1) {} else {} }\n\n  fun h() { if(1) {} else { x = 5; } }\n\n  fun i() { if(1) {} }\n\n  fun j() { if(1) { x = 5; } else { } }\n  "
-- globals1
#guard accepts "\n  var 1 x = 1+1;\n  "
-- globals2
#guard accepts "\n  var 1 x = 1+1;\n\n  fun f() { x = x + 1; return x; }\n\n  var 1 y = x+1;\n  "
-- globals3
#guard accepts "\n  var 1 x = 0;\n\n  fun f(1 y) { x = y + 1; var x = 5; return x; }\n  "
-- globals4
#guard accepts "\n  var 1 x = 0;\n\n  fun f(1 y) { x = f(x); var x = 5; x = f(x); return x; }\n  "
-- empty_dec_prog
#guard accepts "\n  fun f() { var x = 0; }\n\n  fun g() { var 1 x = f(); }\n  "
-- opt_shape_dec
#guard accepts "\n  var 1 x = 0;\n  var y = 0;\n\n  fun 1 f(1 a) {\n    x = a + 1;\n    var 1 z = f(a);\n    var 1 x = 5;\n    return x;\n  }\n\n  fun g(b) {\n    y = b + 1;\n    var z = g(a);\n    var y = 5;\n    return y;\n  }\n  "
-- add_with_carry_ex
#guard accepts "\n  fun {1,1} f() {\n    var a = 1;\n    var b = 2;\n    var c = 0;\n    var {1,1} r = __add_with_carry__(a, b, c);\n    r = __add_with_carry__(a, b, c);\n    return r;\n  }"
-- named_structs
#guard accepts "\n  struct my_struct {\n    2 tuple,\n    1 value\n  }\n\n  struct my_other_struct {\n    my_struct s\n  }\n\n  fun my_struct f(my_struct a) {\n    return my_struct <tuple = a.tuple, value = a.value>;\n  }\n\n  fun my_struct g() {\n    var my_struct x = my_struct <tuple = <0,1>, value = 2>;\n    return f(x);\n  }\n  "
-- exception_declaration
#guard accepts "\n  exception ExampleException : 1;\n\n  fun f() { throw ExampleException 1; }\n\n  fun g() {\n    var 1 x = 0;\n    var 1 y = 0;\n    try\n      y = f()\n    catch ExampleException => x {\n      y = x + 1;\n    }\n    return y;\n  }\n  "

-- Malformed inputs upstream rejects. These are the interesting ones: the
-- error follows non-recursive block comments, so comment handling must not
-- swallow it.
-- error_line_ex1
#guard rejects "/* this\n  nasty /* non recursive /*\n  block comment\n  */\n  // and these\n  // single-line comments\n  fun fun main() { //should not interfer with error line reporting\n    return /* nor should this */ 1;\n  }\n "
-- error_line_ex2
#guard rejects "/* this\n  nasty /* non recursive /*\n  block comment\n  */\n  // and these\n  // single-line comments\n  fun main() { //should not interfer with error line reporting\n    return val /* nor should this */ 1;\n  }\n "
-- error_line_ex3
#guard rejects "\n  fun foo() {\n    skip;\n    while (1) {\n      skip;\n      skip;\n      skeep;\n      skip;\n    }\n  }\n"

end Flapjack.Test.Parser
