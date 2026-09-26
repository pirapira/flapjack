import Flapjack.Parser
import Flapjack.Pancake.PanStatic
import Flapjack.Pancake.PanToCrep.Compile

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

/-! Cake's `collect_globals_def` keeps only top-level `Decl` entries, ignores
    functions/exceptions/structures, and has earlier declarations win when a
    name is repeated (`panPtreeConversionScript.sml:816-821`). -/
def collectGlobalsCakeParity : Bool :=
  let function : FunDecl Int :=
    { name := "f", inline := false, exported := false,
      params := [], body := .skip, returnShape := .one }
  let declarations : List (Decl Int) :=
    [.function function,
      .decl .one "g" (.const 1),
      .exnDecl "E" .one,
      .decl .one "g" (.const 2),
      .name "S" [],
      .decl .one "h" (.const 3)]
  let globals := collectGlobals declarations
  lookupInfo "g" globals == some () &&
    lookupInfo "h" globals == some () &&
    lookupInfo "f" globals == none &&
    lookupInfo "E" globals == none

#guard collectGlobalsCakeParity

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

/-! `isAtom_singleton_def` is the Cake lexer boundary at
    `cakeml/pancake/parser/panLexerScript.sml:46`: exactly the listed
    punctuation characters are emitted as one-character atoms.  The guard
    checks the complete source set and representative adjacent non-members;
    `nextAtom` consumes this predicate directly. -/
def isAtomSingletonCakeParity : Bool :=
  ("+-^*().,;:[]{}".toList).all isAtomSingleton &&
  ("0a#=<>!&|".toList).all (fun character => !isAtomSingleton character)

#guard isAtomSingletonCakeParity

/-! Cake's symbolic-group boundaries are `isAtom_begin_group_def` and
    `isAtom_in_group_def` at `panLexerScript.sml:50,57`.  These guards cover
    each complete source character set and nearby non-members; `nextAtom`
    uses both predicates when collecting symbolic tokens. -/
def isAtomGroupCakeParity : Bool :=
  ("#=><!&|".toList).all isAtomBeginGroup &&
  ("+-^*().,;:{}[]0a".toList).all (fun character => !isAtomBeginGroup character) &&
  ("=<>|&+".toList).all isAtomInGroup &&
  ("#$^*().,;:{}[]0a".toList).all (fun character => !isAtomInGroup character)

#guard isAtomGroupCakeParity

/-! Cake `isAlphaNumOrWild_def` (`panLexerScript.sml:61`) accepts every
    alphanumeric character plus underscore, and rejects nearby punctuation. -/
def isAlphaNumOrWildCakeParity : Bool :=
  ['a', 'Z', '0', '9', '_'].all isAlphaNumOrWild &&
    ['-', '+', '.', '@', ' '].all (fun character => !isAlphaNumOrWild character)

#guard isAlphaNumOrWildCakeParity

/-! Cake `read_while_def` (`panLexerScript.sml:166`) returns the accepted
    prefix in source order and leaves the first rejected character plus its
    suffix untouched. -/
def readWhileCakeParity : Bool :=
  let letters : Char → Bool := fun character => character == 'a' || character == 'b'
  sameAst (readWhile letters "ababaX".toList []) ("ababa", "X".toList) &&
    sameAst (readWhile letters "Xab".toList []) ("", "Xab".toList) &&
    sameAst (readWhile letters "ab".toList ['z']) ("zab", ([] : List Char))

#guard readWhileCakeParity

/-! Cake `next_atom_def` (`panLexerScript.sml:225`) skips whitespace and
    newlines, recognizes unsigned/signed numbers, words, singleton symbols,
    and reports an unrecognized character without silently dropping it. -/
def nextAtomCakeParity : Bool :=
  match nextAtom 16 " \n42".toList initLoc,
      nextAtom 16 "-17".toList initLoc,
      nextAtom 16 "name".toList initLoc,
      nextAtom 16 "+".toList initLoc,
      nextAtom 16 "`".toList initLoc,
      nextAtom 16 "".toList initLoc with
  | some (.numberA 42, numberLoc, []),
      some (.numberA (-17), signedLoc, []),
      some (.wordA "name", wordLoc, []),
      some (.symA "+", symbolLoc, []),
      some (.errA "Unrecognised symbol: `", errorLoc, _), none =>
      numberLoc == { start := .posn 2 0, stop := .posn 2 2 } &&
        signedLoc == { start := .posn 1 1, stop := .posn 1 3 } &&
        wordLoc == { start := .posn 1 1, stop := .posn 1 5 } &&
        symbolLoc == { start := .posn 1 1, stop := .posn 1 1 } &&
        errorLoc == { start := .posn 1 1, stop := .posn 1 1 }
  | _, _, _, _, _, _ => false

#guard nextAtomCakeParity

/-! Cake `next_token_def` (`panLexerScript.sml:284`) maps the atom returned by
    `next_atom` through `token_of_atom`, preserving locations and remaining
    input, while propagating EOF as `NONE`. -/
def nextTokenCakeParity : Bool :=
  match nextToken 16 "42".toList initLoc,
      nextToken 16 "skip".toList initLoc,
      nextToken 16 "?".toList initLoc,
      nextToken 16 "".toList initLoc with
  | some (.intT 42, numberLoc, []),
      some (.keywordT .skipK, keywordLoc, []),
      some (.lexErrorT "Unrecognised symbol: ?", errorLoc, []), none =>
      numberLoc == { start := .posn 1 1, stop := .posn 1 3 } &&
        keywordLoc == { start := .posn 1 1, stop := .posn 1 5 } &&
        errorLoc == { start := .posn 1 1, stop := .posn 1 1 }
  | _, _, _, _ => false

#guard nextTokenCakeParity

/-! Cake `token_of_atom_def` (`panLexerScript.sml:156`) maps each atom
    constructor through the corresponding token conversion, preserving every
    payload and using Cake's keyword/symbol tables for words and symbols. -/
def tokenOfAtomCakeParity : Bool :=
  tokenOfAtom (.numberA (-7)) == .intT (-7) &&
    tokenOfAtom (.wordA "skip") == .keywordT .skipK &&
    tokenOfAtom (.symA "+") == .plusT &&
    tokenOfAtom (.errA "bad") == .lexErrorT "bad" &&
    tokenOfAtom (.annotCommentA "note") == .annotCommentT "note"

#guard tokenOfAtomCakeParity

/-! Cake `dest_lexErrorT_def` (`panLexerScript.sml:70`) projects the message
    from a `LexErrorT` and rejects every other token constructor. -/
def destLexErrorTCakeParity : Bool :=
  destLexErrorT (.lexErrorT "bad") == some "bad" &&
    destLexErrorT (.intT 7) == none &&
    destLexErrorT (.keywordT .skipK) == none

#guard destLexErrorTCakeParity

/-! Cake `isLexErrorT_def` (`panLexerScript.sml:65`) recognizes exactly the
    `LexErrorT` token constructor and rejects representative ordinary tokens. -/
def isLexErrorTCakeParity : Bool :=
  isLexErrorT (.lexErrorT "bad") &&
    !isLexErrorT (.intT 7) &&
    !isLexErrorT (.keywordT .skipK) &&
    !isLexErrorT (.identT "name")

#guard isLexErrorTCakeParity

/-! Cake `get_token_def` (`panLexerScript.sml:75`) is an ordered symbolic-token
    lookup.  Exercise every source branch and the final lexical-error fallback. -/
def getTokenCakeParity : Bool :=
  let cases : List (String × Token) := [
    ("&&", .boolAndT), ("||", .boolOrT), ("&", .andT), ("|", .orT),
    ("^", .xorT), ("==", .eqT), ("=>", .arrowT), ("!=", .neqT),
    ("<", .lessT), (">", .greaterT), (">=", .geqT), ("<=", .leqT),
    ("<+", .lowerT), (">+", .higherT), (">=+", .higheqT), ("<=+", .loweqT),
    ("!", .notT), ("+", .plusT), ("-", .minusT), ("*", .starT),
    (".", .dotT), ("<<", .lslT), (">>>", .lsrT), (">>", .asrT),
    ("#>>", .rorT), ("(", .lParT), (")", .rParT), (",", .commaT),
    (";", .semiT), (":", .colonT), ("[", .lBrakT), ("]", .rBrakT),
    ("{", .lCurT), ("}", .rCurT), ("=", .assignT)]
  cases.all (fun (source, expected) => getToken source == expected) &&
    getToken "?" == .lexErrorT "Unrecognised symbolic token: ?"

#guard getTokenCakeParity

/-! Cake `init_loc_def` (`panLexerScript.sml:299`) starts lexing at row 1,
    column 1. -/
def initLocCakeParity : Bool :=
  sameAst initLoc (.posn 1 1)

#guard initLocCakeParity

/-! Cake `next_line_def` (`panLexerScript.sml:186`) increments the row and
    resets the column for a concrete position, while preserving EOF/unknown
    sentinel positions. -/
def nextLineCakeParity : Bool :=
  sameAst (nextLine (.posn 7 42)) (.posn 8 0) &&
    sameAst (nextLine .eofPt) (.eofPt) &&
    sameAst (nextLine .unknownPt) (.unknownPt)

#guard nextLineCakeParity

/-! Cake `skip_comment_def` (`panLexerScript.sml:195`) stops at the first
    newline, returns its post-newline location and consumed count, and fails
    when the comment reaches EOF without a newline. -/
def skipCommentCakeParity : Bool :=
  match skipComment "abc\nrest".toList initLoc 0,
      skipComment "abc".toList initLoc 0,
      skipComment [] initLoc 0 with
  | some (loc, count), none, none =>
      sameAst loc (.posn 2 0) && count == 4
  | _, _, _ => false

#guard skipCommentCakeParity

/-! Cake `skip_block_comment_def` (`panLexerScript.sml:205`) returns the
    post-delimiter position, characters-inside count, and drop count.  The
    newline case is included because it exercises the intermediate position
    transition rather than only the final parser result. -/
def skipBlockCommentCakeParity : Bool :=
  match skipBlockComment "abc*/rest".toList (.posn 1 3) 0,
      skipBlockComment "a\nb*/rest".toList (.posn 1 3) 0,
      skipBlockComment "ab@/rest".toList (.posn 1 3) 0,
      skipBlockComment ['x'] (.posn 1 3) 0 with
  | some (plainLoc, plainCount, plainDrop),
      some (newlineLoc, newlineCount, newlineDrop),
      some (altLoc, altCount, altDrop), none =>
      sameAst (plainLoc, plainCount, plainDrop) ((.posn 1 8), 3, 5) &&
        sameAst (newlineLoc, newlineCount, newlineDrop) ((.posn 2 3), 3, 5) &&
        sameAst (altLoc, altCount, altDrop) ((.posn 1 7), 2, 4)
  | _, _, _, _ => false

#guard skipBlockCommentCakeParity

/-! Cake `varkind_to_str_def` (`pan_passesScript.sml:124-127`) preserves the
    two source variable-kind display names exactly. -/
def varKindToStringCakeParity : Bool :=
  varKindToString .global == "global" &&
    varKindToString .local == "local"

#guard varKindToStringCakeParity

/-! Cake `pan_seqs_def` (`pan_passesScript.sml:184-190`) flattens ordinary
    sequences but preserves a sequence whose first item is an annotation. -/
def panSeqsCakeParity : Bool :=
  let ordinary : Prog Int :=
    .seq (.seq .skip .tick) (.assign .local "x" (.const 7))
  let annotated : Prog Int :=
    .seq (.annot "@" "note") (.assign .local "x" (.const 7))
  sameAst (panSeqs ordinary)
      ([.skip, .tick, .assign .local "x" (.const 7)] : List (Prog Int)) &&
    sameAst (panSeqs annotated) ([annotated] : List (Prog Int)) &&
    sameAst (panSeqs (.tick : Prog Int)) ([.tick] : List (Prog Int))

#guard panSeqsCakeParity

/-! Cake `unhex_alt_def` (`panLexerScript.sml:217`) returns the `UNHEX` value
    for decimal and upper/lowercase hexadecimal digits, and zero otherwise. -/
def unhexAltCakeParity : Bool :=
  [unhexAlt '0', unhexAlt '9', unhexAlt 'a', unhexAlt 'f',
   unhexAlt 'A', unhexAlt 'F', unhexAlt 'g', unhexAlt ' ']
    == [0, 9, 10, 15, 10, 15, 0, 0]

#guard unhexAltCakeParity

/-! Cake `num_from_dec_string_alt_def` (`panLexerScript.sml:221`) is
    `s2n 10 unhex_alt`; these cases cover its empty/leading-zero and
    multi-digit accumulation, plus the signed `next_atom` caller. -/
def numFromDecStringAltCakeParity : Bool :=
  numFromDecStringAlt "" == 0 &&
    numFromDecStringAlt "00042" == 42 &&
    numFromDecStringAlt "12345" == 12345 &&
    match nextAtom 16 "-42".toList initLoc with
    | some (.numberA (-42), _, []) => true
    | _ => false

#guard numFromDecStringAltCakeParity

/-! Cake `loc_row_def` (`panLexerScript.sml:191`) constructs a position at the
    requested row and the initial source column. -/
def locRowCakeParity : Bool :=
  sameAst (locRow 0) (.posn 0 1) &&
    sameAst (locRow 17) (.posn 17 1)

#guard locRowCakeParity

/-! Cake `next_loc_def` (`panLexerScript.sml:181`) advances only the column
    of a concrete `POSN`; the EOF and unknown sentinels are unchanged. -/
def nextLocCakeParity : Bool :=
  nextLoc 0 (.posn 4 5) == .posn 4 5 &&
    nextLoc 3 (.posn 4 5) == .posn 4 8 &&
    nextLoc 3 .eofPt == .eofPt &&
    nextLoc 3 .unknownPt == .unknownPt

#guard nextLocCakeParity

/-! Cake `pancake_lex_aux_def` (`panLexerScript.sml:303`) accumulates tokens in
    source order, threads each token's end location into the next call, and
    returns an empty list at EOF or exhausted fuel. -/
def pancakeLexAuxCakeParity : Bool :=
  let source := "x + 1"
  let expected := [
    (.identT "x", { start := .posn 1 1, stop := .posn 1 2 }),
    (.plusT, { start := .posn 1 3, stop := .posn 1 3 }),
    (.intT 1, { start := .posn 1 4, stop := .posn 1 5 })]
  sameAst (lexAux (source.length + 1) source.toList initLoc) expected &&
    sameAst (lexAux 0 source.toList initLoc) [] &&
    sameAst (lexAux 16 "".toList initLoc) []

#guard pancakeLexAuxCakeParity

/-! Cake `pancake_lex_def` (`panLexerScript.sml:314`) invokes the auxiliary
    lexer at `init_loc`; the public entrypoint therefore exposes the same
    token stream and source locations as the direct auxiliary oracle. -/
def pancakeLexCakeParity : Bool :=
  let source := "x + 1"
  let expected := [
    (.identT "x", { start := .posn 1 1, stop := .posn 1 2 }),
    (.plusT, { start := .posn 1 3, stop := .posn 1 3 }),
    (.intT 1, { start := .posn 1 4, stop := .posn 1 5 })]
  sameAst (pancakeLex source) expected &&
    sameAst (pancakeLex "") []

#guard pancakeLexCakeParity

/-! Cake `posn_string_def` (`panPtreeConversionScript.sml:534`) renders all
    source-position constructors exactly, including the two sentinel values.
    The strings are the intermediate values consumed by `locs_comment`. -/
def posnStringCakeParity : Bool :=
  posnString (.posn 12 34) == "12:34" &&
    posnString .eofPt == "EOF" &&
    posnString .unknownPt == "UNKNOWN"

#guard posnStringCakeParity

/-! `isNT_def` and `argsNT_def` at
    `panPtreeConversionScript.sml:58,62` inspect only the node's
    nonterminal: matching nodes succeed, mismatching nodes and leaves do not. -/
def parseTreeNtCakeParity : Bool :=
  let matching : ParseTree := .nd .exp [] unknownLoc
  let mismatching : ParseTree := .nd .prog [] unknownLoc
  let leaf : ParseTree := .lf .semiT unknownLoc
  ParseTree.isNT matching .exp &&
    !ParseTree.isNT mismatching .exp &&
    !ParseTree.isNT leaf .exp &&
    match ParseTree.argsNT matching .exp, ParseTree.argsNT mismatching .exp,
      ParseTree.argsNT leaf .exp with
    | some [], none, none => true
    | _, _, _ => false

#guard parseTreeNtCakeParity

/-! Cake `parsetree_locs_def` (`panPtreeConversionScript.sml:527`) projects
    the stored location pair from either a leaf or a node without inspecting
    its token, nonterminal, or children. -/
def parseTreeLocsCakeParity : Bool :=
  let leafLoc : Locs := { start := .posn 2 3, stop := .posn 2 7 }
  let nodeLoc : Locs := { start := .posn 5 1, stop := .eofPt }
  ParseTree.locs (.lf (.identT "x") leafLoc) == leafLoc &&
    ParseTree.locs (.nd .exp [] nodeLoc) == nodeLoc

#guard parseTreeLocsCakeParity

/-! Cake `destLf_def` (`panPtreeConversionScript.sml:25`) projects the token
    from a leaf and returns `NONE` for a non-leaf node.  Lean's `destTok` is
    the corresponding `destTOK ∘ destLf` composition. -/
def destLfCakeParity : Bool :=
  ParseTree.destTok (.lf (.identT "x") unknownLoc) == some (.identT "x") &&
    ParseTree.destTok (.nd .prog [] unknownLoc) == none

#guard destLfCakeParity

/-! Cake `destTOK_def` (`panPtreeConversionScript.sml:29`) then projects the
    token constructor from the `TOK` wrapper; the composed Lean operation
    preserves every token payload and rejects a node. -/
def destTokCakeParity : Bool :=
  match ParseTree.destTok (.lf (.intT (-9)) unknownLoc),
      ParseTree.destTok (.nd .exp [] unknownLoc) with
  | some (.intT (-9)), none => true
  | _, _ => false

#guard destTokCakeParity

/-! Cake `tokcheck_def` (`panPtreeConversionScript.sml:40`) compares a leaf's
    token with the expected token and returns false for a non-leaf. -/
def tokcheckCakeParity : Bool :=
  let plus : ParseTree := .lf (.plusT) unknownLoc
  let node : ParseTree := .nd .exp [] unknownLoc
  ParseTree.tokcheck plus .plusT &&
    !ParseTree.tokcheck plus .minusT &&
    !ParseTree.tokcheck node .plusT

#guard tokcheckCakeParity

/-! Cake `dest_annot_tok_def` (`panPtreeConversionScript.sml:48`) extracts
    only an `AnnotCommentT` payload from a leaf; ordinary tokens and nodes are
    rejected. -/
def destAnnotTokCakeParity : Bool :=
  match destAnnotTok (.lf (.annotCommentT " note ") unknownLoc),
      destAnnotTok (.lf (.identT "x") unknownLoc),
      destAnnotTok (.nd .prog [] unknownLoc) with
  | some " note ", none, none => true
  | _, _, _ => false

#guard destAnnotTokCakeParity

/-! Cake `kw_def` (`panPtreeConversionScript.sml:54`) wraps a keyword enum in
    the corresponding `KeywordT` token without changing its constructor. -/
def kwCakeParity : Bool :=
  let kw (keyword : Keyword) : Token := .keywordT keyword
  kw .varK == .keywordT .varK && kw .retK == .keywordT .retK

#guard kwCakeParity

/-! Cake's leaf converters at
    `panPtreeConversionScript.sml:90,97,104` accept only their respective
    token constructors: identifiers become global variables, while foreign
    identifiers remain FFI names. -/
def convIdentCakeParity : Bool :=
  let ident : ParseTree := .lf (.identT "x") unknownLoc
  let foreign : ParseTree := .lf (.foreignIdent "write") unknownLoc
  let integer : ParseTree := .lf (.intT 7) unknownLoc
  match convIdent ident, convIdent foreign,
      convFfiIdent foreign, convFfiIdent ident,
      convVar (α := Nat) ident, convVar (α := Nat) integer with
  | some "x", none, some "write", none, some (.var .global "x"), none => true
  | _, _, _, _, _, _ => false

#guard convIdentCakeParity

/-! Cake `conv_int_def` (`panPtreeConversionScript.sml:72`) accepts an
    integer leaf, including negative and zero values, and rejects non-integer
    leaves and non-leaf parse-tree nodes. -/
def convIntCakeParity : Bool :=
  convInt (.lf (.intT (-17)) unknownLoc) == some (-17) &&
    convInt (.lf (.intT 0) unknownLoc) == some 0 &&
    convInt (.lf (.identT "x") unknownLoc) == none &&
    convInt (.nd .exp [] unknownLoc) == none

#guard convIntCakeParity

/-! Cake `conv_nat_def` (`panPtreeConversionScript.sml:79`) delegates to
    `conv_int`, converts nonnegative integers to naturals, and rejects negative
    or non-integer leaves. -/
def convNatCakeParity : Bool :=
  convNat (.lf (.intT 17) unknownLoc) == some 17 &&
    convNat (.lf (.intT 0) unknownLoc) == some 0 &&
    convNat (.lf (.intT (-1)) unknownLoc) == none &&
    convNat (.lf (.identT "x") unknownLoc) == none

#guard convNatCakeParity

/-! Cake `conv_const_def` (`panPtreeConversionScript.sml:86`) maps the
    integer leaf through `i2w` and wraps it as `Const`; non-integer leaves stay
    absent.  `ofI` is the test-width identity supplied to the parameterized
    Lean port. -/
def convConstCakeParity : Bool :=
  sameAst (convConst ofI (.lf (.intT (-17)) unknownLoc))
      (some (.const (-17))) &&
    sameAst (convConst ofI (.lf (.intT 0) unknownLoc))
      (some (.const 0)) &&
    sameAst (convConst ofI (.lf (.identT "x") unknownLoc))
      (none : Option (Exp Int))

#guard convConstCakeParity

/-! Cake `binaryExps_def` (`panPtreeConversionScript.sml:109`) enumerates the
    left-associative binary expression nonterminals in source order.  Each
    listed node uses the shared fold, while a non-listed node is not part of
    this family. -/
def binaryExpsCakeParity : Bool :=
  let integer (value : Int) : ParseTree := .lf (.intT value) unknownLoc
  let binary (nonterminal : Nonterminal) (token : Token)
      (operator : BinOp) : Bool :=
    sameAst (convExp ofI 8
        (.nd nonterminal
          [integer 1, .lf token unknownLoc, integer 2] unknownLoc))
      (some (.op operator [.const 1, .const 2]))
  sameAst ([.eOr, .eXor, .eAnd, .eAdd] : List Nonterminal)
      [.eOr, .eXor, .eAnd, .eAdd] &&
    binary .eOr .orT .or && binary .eXor .xorT .xor &&
    binary .eAnd .andT .and && binary .eAdd .plusT .add

#guard binaryExpsCakeParity

/-! Cake `panExps_def` (`panPtreeConversionScript.sml:113`) is the singleton
    `EMulNT` family consumed by `conv_panops`; other expression nodes stay out
    of that fold. -/
def panExpsCakeParity : Bool :=
  let integer (value : Int) : ParseTree := .lf (.intT value) unknownLoc
  sameAst panExps ([.eMul] : List Nonterminal) &&
    sameAst (convExp ofI 8
      (.nd .eMul [integer 3, .lf (.starT) unknownLoc, integer 4] unknownLoc))
      (some (.panOp .mul [.const 3, .const 4])) &&
    (convExp ofI 8
      (.nd .eAdd [integer 3, .lf (.plusT) unknownLoc, integer 4] unknownLoc)).isSome

#guard panExpsCakeParity

/-! Cake `isSubOp_def` (`panPtreeConversionScript.sml:119`) is true only for
    a binary `Sub` expression; it prevents subtraction from being flattened
    with other binary operators. -/
def isSubOpCakeParity : Bool :=
  isSubOp (.op .sub [.const (1 : Int), .const 2]) &&
    !isSubOp (.op .sub [.const (1 : Int), .const 2, .const 3]) &&
    !isSubOp (.op .add [.const (1 : Int), .const 2]) &&
    !isSubOp (.panOp .mul [.const (1 : Int), .const 2])

#guard isSubOpCakeParity

/-! Cake `conv_Exp_def` (`panPtreeConversionScript.sml:244`) dispatches
    expression nodes in source order, while leaves fall through to constants
    and variables; malformed node shapes return `NONE`. -/
def convExpCakeParity : Bool :=
  let integer (value : Int) : ParseTree := .lf (.intT value) unknownLoc
  let identifier (name : String) : ParseTree := .lf (.identT name) unknownLoc
  let notToken : ParseTree := .lf (.notT) unknownLoc
  sameAst (convExp ofI 8 (integer 7)) (some (.const 7)) &&
    sameAst (convExp ofI 8 (identifier "x")) (some (.var .global "x")) &&
    sameAst (convExp ofI 8
      (.nd .eNot [integer 7] unknownLoc)) (some (.const 7)) &&
    sameAst (convExp ofI 8
      (.nd .eNot [notToken, integer 7] unknownLoc))
      (some (.cmp .equal (.const 0) (.const 7))) &&
    sameAst (convExp ofI 8
      (.nd .eField [integer 7, integer 2] unknownLoc))
      (some (.rField 2 (.const 7))) &&
    sameAst (convExp ofI 8 (.nd .eField [] unknownLoc))
      (none : Option (Exp Int))

#guard convExpCakeParity

/-! Cake `conv_NonRecStmt_def` (`panPtreeConversionScript.sml:404`) converts
    statements without nested `Prog` children, including assignment, memory,
    shared-memory load, return, raise, and the leaf control statements. -/
def convNonRecStmtCakeParity : Bool :=
  let integer (value : Int) : ParseTree := .lf (.intT value) unknownLoc
  let identifier (name : String) : ParseTree := .lf (.identT name) unknownLoc
  let assignTree := .nd .assign [identifier "x", integer 7] unknownLoc
  let storeTree := .nd .store [integer 8, integer 9] unknownLoc
  let sharedLoadTree := .nd .sharedLoad [identifier "x", integer 10] unknownLoc
  let returnTree := .nd .returnNT [integer 11] unknownLoc
  let raiseTree := .nd .throwNT [identifier "E", integer 12] unknownLoc
  let malformed := .nd .assign [identifier "x"] unknownLoc
  sameAst (convNonRecStmt ofI 8 assignTree)
      (some (.assign .global "x" (.const 7))) &&
    sameAst (convNonRecStmt ofI 8 storeTree)
      (some (.store (.const 8) (.const 9))) &&
    sameAst (convNonRecStmt ofI 8 sharedLoadTree)
      (some (.shMemLoad .opW .global "x" (.const 10))) &&
    sameAst (convNonRecStmt ofI 8 returnTree)
      (some (.return (.const 11))) &&
    sameAst (convNonRecStmt ofI 8 raiseTree)
      (some (.raise "E" (.const 12))) &&
    sameAst (convNonRecStmt ofI 8 (.lf (.keywordT .skipK) unknownLoc))
      (some .skip) &&
    sameAst (convNonRecStmt ofI 8 malformed)
      (none : Option (Prog Int))

#guard convNonRecStmtCakeParity

/-! Cake `butlast_def` (`panPtreeConversionScript.sml:487`) drops exactly the
    final list element, including the empty and singleton boundary cases. -/
def butlastCakeParity : Bool :=
  butlast ([] : List Nat) == [] &&
    butlast [7] == [] &&
    butlast [1, 2, 3, 4] == [1, 2, 3]

#guard butlastCakeParity

/-! Cake operator conversion at `panPtreeConversionScript.sml:141,153,168`
    recurses through the corresponding operator wrapper, maps comparison
    spellings to `(Cmp, swapped)`, and rejects other wrappers/tokens. -/
def convOperatorCakeParity : Bool :=
  let star : ParseTree := .lf (.starT) unknownLoc
  let mulNode : ParseTree := .nd .mulOps [star] unknownLoc
  let ror : ParseTree := .lf (.rorT) unknownLoc
  let shiftNode : ParseTree := .nd .shiftOps [ror] unknownLoc
  let greater : ParseTree := .lf (.greaterT) unknownLoc
  let cmpNode : ParseTree := .nd .cmpOps [greater] unknownLoc
  let equal : ParseTree := .lf (.eqT) unknownLoc
  let eqNode : ParseTree := .nd .eqOps [equal] unknownLoc
  let wrong : ParseTree := .lf (.plusT) unknownLoc
  match convPanop mulNode, convShift shiftNode, convCmp cmpNode,
      convCmp eqNode, convPanop wrong, convShift wrong, convCmp wrong with
  | some .mul, some .ror, some (.less, true), some (.equal, false),
      none, none, none => true
  | _, _, _, _, _, _, _ => false

#guard convOperatorCakeParity

/-! Cake's `conv_params_def` (`panPtreeConversionScript.sml:224`) consumes a
    flat sequence of shape/name pairs, accepts the empty list, and rejects an
    incomplete pair or a pair whose shape/name conversion fails. -/
def convParamsCakeParity : Bool :=
  let one : ParseTree := .lf (.intT 1) unknownLoc
  let x : ParseTree := .lf (.identT "x") unknownLoc
  let y : ParseTree := .lf (.identT "y") unknownLoc
  let wrong : ParseTree := .lf (.plusT) unknownLoc
  match convParams 8 [one, x, one, y], convParams 8 [],
      convParams 8 [one], convParams 8 [wrong, x] with
  | some [("x", .one), ("y", .one)], some [], none, none => true
  | _, _, _, _ => false

#guard convParamsCakeParity

/-! Cake location conversion at `panPtreeConversionScript.sml:540,549`
    renders both position forms and prepends a `location` annotation only
    when requested. -/
def locationAnnotationCakeParity : Bool :=
  let locs : Locs := { start := .posn 2 3, stop := .eofPt }
  let tree : ParseTree := .lf (.identT "x") locs
  match locsComment locs, addLocsAnnot true tree (.skip : Prog Nat),
      addLocsAnnot false tree (.skip : Prog Nat) with
  | "(2:3 EOF)", .seq (.annot "location" "(2:3 EOF)") .skip, .skip => true
  | _, _, _ => false

#guard locationAnnotationCakeParity

/-! Cake `conv_Dec_def` (`panPtreeConversionScript.sml:555`) accepts exactly
    a `DecNT` node with shape, identifier, and expression children; malformed
    arity or a different nonterminal returns `NONE`. -/
def convDecCakeParity : Bool :=
  let one : ParseTree := .lf (.intT 1) unknownLoc
  let x : ParseTree := .lf (.identT "x") unknownLoc
  let value : ParseTree := .lf (.intT 7) unknownLoc
  let valid : ParseTree := .nd .dec [one, x, value] unknownLoc
  let wrongNode : ParseTree := .nd .prog [one, x, value] unknownLoc
  let short : ParseTree := .nd .dec [one, x] unknownLoc
  match convDecForm (fun value => value) 8 .dec valid,
      convDecForm (fun value => value) 8 .dec wrongNode,
      convDecForm (fun value => value) 8 .dec short with
  | some (.one, "x", .const 7), none, none => true
  | _, _, _ => false

#guard convDecCakeParity

/-! Cake `conv_GlobalDec_def` (`panPtreeConversionScript.sml:571`) shares the
    declaration shape conversion but requires a `GlobalDecNT` node; a local
    declaration node or malformed arity returns `NONE`. -/
def convGlobalDecCakeParity : Bool :=
  let one : ParseTree := .lf (.intT 1) unknownLoc
  let x : ParseTree := .lf (.identT "g") unknownLoc
  let value : ParseTree := .lf (.intT 9) unknownLoc
  let valid : ParseTree := .nd .globalDec [one, x, value] unknownLoc
  let wrongNode : ParseTree := .nd .dec [one, x, value] unknownLoc
  let short : ParseTree := .nd .globalDec [one, x] unknownLoc
  match convDecForm (fun value => value) 8 .globalDec valid,
      convDecForm (fun value => value) 8 .globalDec wrongNode,
      convDecForm (fun value => value) 8 .globalDec short with
  | some (.one, "g", .const 9), none, none => true
  | _, _, _ => false

#guard convGlobalDecCakeParity

/-! Cake `conv_ExnDec_def` (`panPtreeConversionScript.sml:587`) accepts an
    `ExnDecNT` exception identifier and shape pair; a different node or
    incomplete pair returns `NONE`. -/
def convExnDecCakeParity : Bool :=
  let exception : ParseTree := .lf (.identT "E") unknownLoc
  let one : ParseTree := .lf (.intT 1) unknownLoc
  let valid : ParseTree := .nd .exnDec [exception, one] unknownLoc
  let wrongNode : ParseTree := .nd .dec [exception, one] unknownLoc
  let short : ParseTree := .nd .exnDec [exception] unknownLoc
  match convExnDec 8 valid, convExnDec 8 wrongNode, convExnDec 8 short with
  | some ("E", .one), none, none => true
  | _, _, _ => false

#guard convExnDecCakeParity

/-! Cake `conv_Ret_def` (`panPtreeConversionScript.sml:615`) distinguishes a
    bare `return`, a `!` no-bind marker, and a bound return target; malformed
    return nodes are rejected. -/
def convRetCakeParity : Bool :=
  let returnToken : ParseTree := .lf (.keywordT .retK) unknownLoc
  let noBind : ParseTree := .lf (.notT) unknownLoc
  let x : ParseTree := .lf (.identT "x") unknownLoc
  let bound : ParseTree := .nd .ret [x] unknownLoc
  let malformed : ParseTree := .nd .ret [] unknownLoc
  match convRet returnToken, convRet noBind, convRet bound, convRet malformed with
  | some none, some (some none), some (some (some (.global, "x"))), none => true
  | _, _, _, _ => false

#guard convRetCakeParity

/-! Cake `conv_Prog_def` (`panPtreeConversionScript.sml:629`) folds a
    `ProgNT` child list into right-nested sequencing; an empty program node is
    rejected rather than silently becoming `skip`. -/
def convProgCakeParity : Bool :=
  let skip : ParseTree := .lf (.keywordT .skipK) unknownLoc
  let breakTree : ParseTree := .lf (.keywordT .brK) unknownLoc
  let sequence : ParseTree := .nd .prog [skip, breakTree] unknownLoc
  let empty : ParseTree := .nd .prog [] unknownLoc
  match convProg (fun value => value) false 8 sequence,
      convProg (fun value => value) false 8 empty with
  | some (.seq .skip .break), none => true
  | _, _ => false

#guard convProgCakeParity

/-! Cake `conv_inline_def` (`panPtreeConversionScript.sml:724`) maps the
    `inline` and `noinline` tokens to `true` and `false`, rejecting unrelated
    leaves. -/
def convInlineCakeParity : Bool :=
  let inlineToken : ParseTree := .lf (.keywordT .inlineK) unknownLoc
  let noInlineToken : ParseTree := .lf (.noinlineT) unknownLoc
  let wrongToken : ParseTree := .lf (.identT "inline") unknownLoc
  match convInline inlineToken, convInline noInlineToken, convInline wrongToken with
  | some true, some false, none => true
  | _, _, _ => false

#guard convInlineCakeParity

/-! Cake `conv_export_def` (`panPtreeConversionScript.sml:732`) maps the
    `export` and `static` tokens to `true` and `false`, rejecting unrelated
    leaves. -/
def convExportCakeParity : Bool :=
  let exportToken : ParseTree := .lf (.keywordT .exportK) unknownLoc
  let staticToken : ParseTree := .lf (.staticT) unknownLoc
  let wrongToken : ParseTree := .lf (.identT "export") unknownLoc
  match convExport exportToken, convExport staticToken, convExport wrongToken with
  | some true, some false, none => true
  | _, _, _ => false

#guard convExportCakeParity

/-! Cake `conv_FieldNameList_def` (`panPtreeConversionScript.sml:740`) passes
    the exact `FieldNameListNT` children to the shaped-parameter converter,
    preserving empty lists and rejecting incomplete pairs. -/
def convFieldNameListCakeParity : Bool :=
  let one : ParseTree := .lf (.intT 1) unknownLoc
  let x : ParseTree := .lf (.identT "field") unknownLoc
  let valid : ParseTree := .nd .fieldNameList [one, x] unknownLoc
  let empty : ParseTree := .nd .fieldNameList [] unknownLoc
  let wrongNode : ParseTree := .nd .paramList [one, x] unknownLoc
  let short : ParseTree := .nd .fieldNameList [one] unknownLoc
  match convFieldNameList 8 valid, convFieldNameList 8 empty,
      convFieldNameList 8 wrongNode, convFieldNameList 8 short with
  | some [("field", .one)], some [], none, none => true
  | _, _, _, _ => false

#guard convFieldNameListCakeParity

/-! Cake `conv_StructName_def` (`panPtreeConversionScript.sml:747`) converts
    the struct identifier together with its shaped field list, preserving an
    empty field list and rejecting malformed structure nodes. -/
def convStructNameCakeParity : Bool :=
  let name : ParseTree := .lf (.identT "S") unknownLoc
  let field : ParseTree := .lf (.identT "f") unknownLoc
  let one : ParseTree := .lf (.intT 1) unknownLoc
  let fields : ParseTree := .nd .fieldNameList [one, field] unknownLoc
  let emptyFields : ParseTree := .nd .fieldNameList [] unknownLoc
  let valid : ParseTree := .nd .structName [name, fields] unknownLoc
  let empty : ParseTree := .nd .structName [name, emptyFields] unknownLoc
  let malformed : ParseTree := .nd .structName [name] unknownLoc
  match convStructName 8 valid, convStructName 8 empty,
      convStructName 8 malformed with
  | some ("S", [("f", .one)]), some ("S", []), none => true
  | _, _, _ => false

#guard convStructNameCakeParity

/-! Cake `conv_TopDec_def` (`panPtreeConversionScript.sml:762`) dispatches
    top-level function, global declaration, struct, and exception nodes to
    their dedicated converters; malformed nodes return `NONE`. -/
def convTopDecCakeParity : Bool :=
  let one : ParseTree := .lf (.intT 1) unknownLoc
  let nine : ParseTree := .lf (.intT 9) unknownLoc
  let name : ParseTree := .lf (.identT "g") unknownLoc
  let field : ParseTree := .lf (.identT "f") unknownLoc
  let exception : ParseTree := .lf (.identT "E") unknownLoc
  let fields : ParseTree := .nd .fieldNameList [one, field] unknownLoc
  let params : ParseTree := .nd .paramList [] unknownLoc
  let function : ParseTree := .nd .funNT
    [.lf (.keywordT .inlineK) unknownLoc, .lf (.staticT) unknownLoc,
      one, .lf (.identT "f") unknownLoc, params,
      .lf (.keywordT .skipK) unknownLoc] unknownLoc
  let global : ParseTree := .nd .globalDec [one, name, nine] unknownLoc
  let structureTree : ParseTree := .nd .structName [
    .lf (.identT "S") unknownLoc, fields] unknownLoc
  let exn : ParseTree := .nd .exnDec [exception, one] unknownLoc
  let malformed : ParseTree := .nd .prog [] unknownLoc
  let functionOk := match convTopDec (fun value => value) false 8 function with
    | some (.function declaration) =>
        declaration.name == "f" && declaration.inline && !declaration.exported &&
          declaration.params.isEmpty &&
          match declaration.body, declaration.returnShape with
          | .skip, .one => true
          | _, _ => false
    | _ => false
  match functionOk,
      convTopDec (fun value => value) false 8 global,
      convTopDec (fun value => value) false 8 structureTree,
      convTopDec (fun value => value) false 8 exn,
      convTopDec (fun value => value) false 8 malformed with
  | true, some (.decl .one "g" (.const 9)),
      some (.name "S" [("f", .one)]),
      some (.exnDecl "E" .one), none => true
  | _, _, _, _, _ => false

#guard convTopDecCakeParity

/-! Cake `conv_TopDecList_def` (`panPtreeConversionScript.sml:788`) preserves
    declaration order, drops annotation-comment leaves, accepts the empty
    list, and rejects malformed child arity. -/
def convTopDecListCakeParity : Bool :=
  let one : ParseTree := .lf (.intT 1) unknownLoc
  let nine : ParseTree := .lf (.intT 9) unknownLoc
  let name : ParseTree := .lf (.identT "g") unknownLoc
  let declaration : ParseTree := .nd .globalDec [one, name, nine] unknownLoc
  let empty : ParseTree := .nd .topDecList [] unknownLoc
  let withDeclaration : ParseTree := .nd .topDecList [declaration, empty] unknownLoc
  let annotation : ParseTree := .lf (.annotCommentT "ignored") unknownLoc
  let withAnnotation : ParseTree :=
    .nd .topDecList [annotation, withDeclaration] unknownLoc
  let malformed : ParseTree := .nd .topDecList [declaration] unknownLoc
  match convTopDecList (fun value => value) false 8 empty,
      convTopDecList (fun value => value) false 8 withDeclaration,
      convTopDecList (fun value => value) false 8 withAnnotation,
      convTopDecList (fun value => value) false 8 malformed with
  | some [], some [.decl .one "g" (.const 9)], some [.decl .one "g" (.const 9)],
      none => true
  | _, _, _, _ => false

#guard convTopDecListCakeParity

/-! Cake `parse_to_ast_def` (`panPtreeConversionScript.sml:809`) exposes the
    single-program parser: a valid sequence converts to the expected AST and
    lexical failure is reported as an error rather than a partial program. -/
def parseToAstCakeParity : Bool :=
  match parseProgram ofI "skip; tick;", parseProgram ofI "skip; `;" with
  | .ok (.seq .skip .tick), .error (_ :: _) => true
  | _, _ => false

#guard parseToAstCakeParity

/-! Cake `localise_exp_def` (`panPtreeConversionScript.sml:824`) changes only
    identifiers present in the scope to `Local`, recursively through expression
    constructors; out-of-scope identifiers stay `Global`. -/
def localiseExpCakeParity : Bool :=
  let expression : Exp Nat :=
    .op .add [.var .global "x", .var .global "y"]
  match localiseExp ["x"] expression,
      localiseExp ["x"] (.load32 (.var .global "x") : Exp Nat) with
  | .op .add [.var .local "x", .var .global "y"],
      .load32 (.var .global "x") => true
  | _, _ => false

#guard localiseExpCakeParity

/-! Cake `localise_topdecs_def` (`panPtreeConversionScript.sml:909`) starts
    each function body in the scope of its parameter names while leaving an
    out-of-scope global unchanged. -/
def localiseTopDecsCakeParity : Bool :=
  let function : Decl Nat := .function
    { name := "f", inline := false, exported := false,
      params := [("a", .one)],
      body := .return (.op .add [.var .global "a", .var .global "g"]),
      returnShape := .one }
  match localiseDecls [function] with
  | [.function declaration] =>
      match declaration.body with
      | .return (.op .add [.var .local "a", .var .global "g"]) => true
      | _ => false
  | _ => false

#guard localiseTopDecsCakeParity

/-! Cake `parse_topdecs_to_ast_def` (`panPtreeConversionScript.sml:913`)
    lexes, converts, and localises a complete declaration list; malformed
    source is reported as an error rather than producing partial declarations. -/
def parseTopDecsCakeParity : Bool :=
  let valid := sameAst (parseTopDecs ofI "var 1 x = 1;")
    (.ok [.decl .one "x" (.const 1)])
  valid && (parseTopDecs ofI "fun f() { return `; }").toOption.isNone

#guard parseTopDecsCakeParity

/-! Cake `mknt_def` (`panPEGScript.sml:36`) wraps child trees in a
    nonterminal node whose location spans the first child's start through the
    last child's stop; an empty child list has `unknownLoc`. -/
def mkNtCakeParity : Bool :=
  let firstLoc : Locs := { start := .posn 2 3, stop := .posn 2 4 }
  let lastLoc : Locs := { start := .posn 2 8, stop := .posn 2 9 }
  let first : ParseTree := .lf (.identT "x") firstLoc
  let last : ParseTree := .lf (.intT 7) lastLoc
  let children : P.Trees := [first, last]
  let expected : Locs := { start := .posn 2 3, stop := .posn 2 9 }
  match P.mkNode .prog children, P.mkSubtree .prog children, P.mkNode .exp [] with
  | .nd .prog _ nodeLoc, [.nd .prog _ subtreeLoc], .nd .exp [] emptyLoc =>
      nodeLoc == expected && subtreeLoc == expected && emptyLoc == unknownLoc
  | _, _, _ => false

#guard mkNtCakeParity

/-! Cake `keep_int_def` (`panPEGScript.sml:90`) keeps only integer tokens,
    packages the original token/location as a leaf, and leaves the parser
    position unchanged on rejection. -/
def keepIntCakeParity : Bool :=
  let accepted : PState :=
    PState.ofToks [(.intT 7, unknownLoc), (.semiT, unknownLoc)]
  let rejected : PState :=
    PState.ofToks [(.identT "x", unknownLoc), (.semiT, unknownLoc)]
  match P.keepInt accepted, P.keepInt rejected with
  | (some [.lf (.intT 7) loc], success), (none, failure) =>
      loc == unknownLoc && success.remaining == 1 && failure.remaining == 2
  | _, _ => false

#guard keepIntCakeParity

/-! Cake `keep_nat_def` (`panPEGScript.sml:96`) keeps non-negative integer
    tokens only; negative integers and other tokens fail without consuming the
    parser input. -/
def keepNatCakeParity : Bool :=
  let accepted : PState :=
    PState.ofToks [(.intT 7, unknownLoc), (.semiT, unknownLoc)]
  let negative : PState :=
    PState.ofToks [(.intT (-1), unknownLoc), (.semiT, unknownLoc)]
  let incompatible : PState :=
    PState.ofToks [(.identT "x", unknownLoc), (.semiT, unknownLoc)]
  match P.keepNat accepted, P.keepNat negative, P.keepNat incompatible with
  | (some [.lf (.intT 7) loc], success), (none, negativeState),
      (none, incompatibleState) =>
      loc == unknownLoc && success.remaining == 1 &&
        negativeState.remaining == 2 && incompatibleState.remaining == 2
  | _, _, _ => false

#guard keepNatCakeParity

/-! Cake `conv_default_shape_def` (`panPtreeConversionScript.sml:189`) accepts
    only the default-shape token and maps it to `One`. -/
def convDefaultShapeCakeParity : Bool :=
  match convDefaultShape (.lf (.defaultShT) unknownLoc),
      convDefaultShape (.lf (.intT 1) unknownLoc),
      convDefaultShape (.lf (.identT "one") unknownLoc) with
  | some .one, none, none => true
  | _, _, _ => false

#guard convDefaultShapeCakeParity

/-! Cake `conv_Shape_def` (`panPtreeConversionScript.sml:197`) accepts
    default, counted, named, and recursive shape-combination trees.  Invalid
    counts, wrong node tags, and exhausted conversion fuel return `NONE`. -/
def convShapeCakeParity : Bool :=
  let defaultTree : ParseTree := .lf (.defaultShT) unknownLoc
  let two : ParseTree := .lf (.intT 2) unknownLoc
  let zero : ParseTree := .lf (.intT 0) unknownLoc
  let negative : ParseTree := .lf (.intT (-1)) unknownLoc
  let named : ParseTree := .lf (.identT "Word") unknownLoc
  let combined : ParseTree := .nd .shapeComb [defaultTree, named] unknownLoc
  let wrongNode : ParseTree := .nd .prog [defaultTree, named] unknownLoc
  match convShape 8 defaultTree,
      convShape 8 two,
      convShape 8 zero,
      convShape 8 negative,
      convShape 8 named,
      convShape 8 combined,
      convShape 0 defaultTree,
      convShape 8 wrongNode with
  | some .one, some (.comb [.one, .one]), none, none,
      some (.named "Word"), some (.comb [.one, .named "Word"]),
      none, none => true
  | _, _, _, _, _, _, _, _ => false

#guard convShapeCakeParity

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
  == [.keywordT .baseK, .keywordT .biwK, .keywordT .baseK, .foreignIdent "write"]

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

/-! Cake `safe_pancake_lex_def` (`panLexerScript.sml:318`) preserves a
    successful token stream, while collecting lexical-error messages and their
    source locations from the filtered output. -/
def safePancakeLexCakeParity : Bool :=
  match safePancakeLex "1 + 2", safePancakeLex "/*" with
  | .ok tokens, .error [(message, loc)] =>
      tokens.map (·.1) == [.intT 1, .plusT, .intT 2] &&
        message == "Malformed comment" &&
        loc == { start := .posn 1 1, stop := .posn 1 3 }
  | _, _ => false

#guard safePancakeLexCakeParity

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

-- Cake's lexer maps `@top` to the `@base` keyword, so conversion preserves
-- the original source behavior and produces `BaseAddr`.
#guard sameAst (expr "@top") (.ok (.return .baseAddr))

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

/-! Direct oracle for `conv_DecCall_def` from
`cakeml/pancake/parser/panPtreeConversionScript.sml:598`.  Cake requires the
first three children (shape, bound name, function name), accepts an omitted
argument-list child as `[]`, and converts only the first optional argument
child. -/
def convDecCallCakeParity : Bool :=
  sameAst
    (convDecCall ofI 16
      (.nd .decCall
        [ .lf (.defaultShT) unknownLoc
        , .lf (.identT "r") unknownLoc
        , .lf (.identT "f") unknownLoc ] unknownLoc))
    (some (.one, "r", "f", [])) &&
  sameAst
    (convDecCall ofI 16
      (.nd .decCall
        [ .lf (.defaultShT) unknownLoc
        , .lf (.identT "r") unknownLoc
        , .lf (.identT "f") unknownLoc
        , .nd .argList
            [ .nd .exp [ .lf (.intT 7) unknownLoc ] unknownLoc ] unknownLoc ]
        unknownLoc))
    (some (.one, "r", "f", [.const 7])) &&
  (convDecCall ofI 16
      (.nd .decCall
        [ .lf (.defaultShT) unknownLoc
        , .lf (.identT "r") unknownLoc ] unknownLoc)).isNone &&
  (convDecCall ofI 16
      (.nd .funNT [] unknownLoc)).isNone

#guard convDecCallCakeParity

-- An annotation comment becomes an `Annot` statement tagged `@`.
#guard sameAst (prog "/@ hello @/ skip;") (.ok (.seq (.annot "@" " hello ") .skip))

/-! ### `__add_with_carry__` -/

/-! Cake `is_add_with_carry_def` (`panPtreeConversionScript.sml:68`) is the
    exact string predicate used to recognize the carry primitive. -/
def isAddWithCarryCakeParity : Bool :=
  addWithCarryName == "__add_with_carry__" &&
    addWithCarryName != "__add_with_carry" &&
    addWithCarryName != "__add_with_carry___"

#guard isAddWithCarryCakeParity

-- As a call it becomes a primitive, taking its result variable from the
-- assignment target.
#guard sameAst (prog "r = __add_with_carry__(a, b, c);")
  (.ok (.primitive "r" .addCarry [.var .global "a", .var .global "b", .var .global "c"]))

-- As a declaration it becomes a declaration of the shape's zero value followed
-- by the primitive. `convProg` obtains this initializer through the exact
-- `shapeValHOL` bridge; the matching One/Comb/Named source-oracle rows are
-- checked in `PanShapeValParity` against `pan_lang_shape_val_probe.out`.
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

/-! Direct oracle for `localise_topdec_def` from
`cakeml/pancake/parser/panPtreeConversionScript.sml:901`.  Non-function
declarations pass through unchanged; a function body is localized under the
parameter-name fold before any nested declaration scope is entered. -/
def localiseTopDecCakeParity : Bool :=
  sameAst
    (localiseDecl (.decl .one "g" (.const 7) : Decl Int))
    (.decl .one "g" (.const 7)) &&
  sameAst
    (localiseDecl (.exnDecl "E" .one : Decl Int))
    (.exnDecl "E" .one) &&
  sameAst
    (localiseDecl (.name "pair" [("left", .one), ("right", .one)] : Decl Int))
    (.name "pair" [("left", .one), ("right", .one)]) &&
  sameAst
    (localiseDecl
      (.function
        { name := "f", inline := false, exported := true,
          params := [("a", .one), ("b", .one)],
          body := .seq
            (.assign .global "a" (.var .global "a"))
            (.return (.var .global "b")),
          returnShape := .one } : Decl Int))
    (.function
      { name := "f", inline := false, exported := true,
        params := [("a", .one), ("b", .one)],
        body := .seq
          (.assign .local "a" (.var .local "a"))
          (.return (.var .local "b")),
        returnShape := .one })

#guard localiseTopDecCakeParity

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

-- Upstream's catch-all localisation leaves `ld32` and `st32` operands marked
-- `Global`; these cases must stay byte- and acceptance-compatible with Cake.
#guard sameAst (prog "var v = 1; return ld32 v;")
  (.ok (.dec "v" .one (.const 1) (.return (.load32 (.var .global "v")))))
#guard sameAst (prog "var v = 1; st32 v, v;")
  (.ok (.dec "v" .one (.const 1) (.store32 (.var .global "v") (.var .global "v"))))

-- Cake rejects a local-only ld32 source name because the catch-all leaves the
-- operand global; keep the acceptance boundary as well as the AST shape.
#guard match parseTopDecs ofI "fun 1 f() {\n  var 1 z = 7;\n  var 1 y = ld32 z;\n  return y;\n}" with
  | .ok declarations => !staticResultOk (staticCheck declarations)
  | .error _ => false

/-! Direct oracle for `localise_prog_def` from
`cakeml/pancake/parser/panPtreeConversionScript.sml:844`.  The scope extends
only over declaration/DecCall bodies and handler bodies; call targets and
arguments use the incoming scope, while primitive destinations remain names
and are not reclassified by this pass. -/
def localiseProgCakeParity : Bool :=
  sameAst
    (localiseProg []
      (.dec "x" .one (.var .global "g")
        (.seq (.assign .global "x" (.var .global "x"))
          (.return (.var .global "g"))) : Prog Int))
    (.dec "x" .one (.var .global "g")
      (.seq (.assign .local "x" (.var .local "x"))
        (.return (.var .global "g")))) &&
  sameAst
    (localiseProg ["x"]
      (.call (some (some (.global, "x"), none)) "f"
        [.var .global "x"] : Prog Int))
    (.call (some (some (.local, "x"), none)) "f"
      [.var .local "x"]) &&
  sameAst
    (localiseProg ["x"]
      (.call (some (some (.global, "x"),
        some ("E", "e", .return (.var .global "e")))) "f"
        [.var .global "x"] : Prog Int))
    (.call (some (some (.local, "x"),
      some ("E", "e", .return (.var .local "e")))) "f"
      [.var .local "x"]) &&
  sameAst
    (localiseProg []
      (.decCall "r" .one "f" [.var .global "g"]
        (.return (.var .global "r")) : Prog Int))
    (.decCall "r" .one "f" [.var .global "g"]
      (.return (.var .local "r")))

#guard localiseProgCakeParity

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

/-! Direct oracle for `consume_kw_def` from
`cakeml/pancake/parser/panPEGScript.sml:64`.  Cake delegates to
`consume_tok (KeywordT k)`: a successful keyword contributes no parse-tree
child and consumes exactly one token, while a mismatch leaves input intact. -/
def consumeKwCakeParity : Bool :=
  let good := P.consumeKw .varK "var"
    (PState.ofToks
      [(.keywordT .varK, unknownLoc), (.semiT, unknownLoc)])
  let bad := P.consumeKw .varK "var"
    (PState.ofToks
      [(.keywordT .funK, unknownLoc), (.semiT, unknownLoc)])
  (match good with
  | (some [], state) => state.remaining == 1 &&
      state.toks == [(.semiT, unknownLoc)] && state.lastConsumed.isSome
  | _ => false) &&
  (match bad with
  | (none, state) => state.remaining == 2 &&
      state.toks == [(.keywordT .funK, unknownLoc), (.semiT, unknownLoc)] &&
      state.furthest.isSome
  | _ => false)

#guard consumeKwCakeParity

/-! Direct oracle for `keep_ffi_ident_def` from
`cakeml/pancake/parser/panPEGScript.sml:84`.  Cake accepts only
`ForeignIdent`, preserves the token in one `mkleaf`, and consumes it. -/
def keepFfiIdentCakeParity : Bool :=
  let good := P.keepFfiIdent
    (PState.ofToks
      [(.foreignIdent "write", unknownLoc), (.semiT, unknownLoc)])
  let bad := P.keepFfiIdent
    (PState.ofToks
      [(.identT "write", unknownLoc), (.semiT, unknownLoc)])
  (match good with
  | (some [.lf (.foreignIdent "write") _], state) =>
      state.remaining == 1 && state.toks == [(.semiT, unknownLoc)] &&
        state.lastConsumed.isSome
  | _ => false) &&
  (match bad with
  | (none, state) => state.remaining == 2 &&
      state.toks == [(.identT "write", unknownLoc), (.semiT, unknownLoc)] &&
      state.furthest.isSome
  | _ => false)

#guard keepFfiIdentCakeParity

/-! Direct oracle for `choicel_def` from
`cakeml/pancake/parser/panPEGScript.sml:106`.  Ordered alternatives use the
first successful parser, while the empty list fails without changing state. -/
def choiceLCakeParity : Bool :=
  let fallback := P.choiceL
      [P.keepKw .funK "fun", P.keepKw .varK "var"]
      (PState.ofToks
        [(.keywordT .varK, unknownLoc), (.semiT, unknownLoc)])
  let first := P.choiceL
      [P.keepKw .varK "var", P.keepKw .funK "fun"]
      (PState.ofToks
        [(.keywordT .varK, unknownLoc), (.semiT, unknownLoc)])
  let empty : Option P.Trees × PState := P.choiceL []
      (PState.ofToks
        [(.keywordT .varK, unknownLoc), (.semiT, unknownLoc)])
  (match fallback with
  | (some [.lf (.keywordT .varK) _], state) => state.remaining == 1
  | _ => false) &&
  (match first with
  | (some [.lf (.keywordT .varK) _], state) => state.remaining == 1
  | _ => false) &&
  (match empty with
  | (none, state) => state.remaining == 2 &&
      state.toks == [(.keywordT .varK, unknownLoc), (.semiT, unknownLoc)] &&
      state.furthest.isNone
  | _ => false)

#guard choiceLCakeParity

/-! Direct oracle for `pegf_def` from
`cakeml/pancake/parser/panPEGScript.sml:111`.  The continuation sees the
first parser result, while failure and parser state are propagated exactly. -/
def pegFCakeParity : Bool :=
  let input : PState := PState.ofToks [(.semiT, unknownLoc)]
  let success := P.pegF (P.pure' 7)
      (fun value => P.pure' (value + 1)) input
  let failureParser : P Nat := fun state => (none, state)
  let failure := P.pegF failureParser (fun _ => P.pure' 1) input
  (match success with
  | (some 8, state) => state.toks == input.toks && state.remaining == 1
  | _ => false) &&
  (match failure with
  | (none, state) => state.toks == input.toks && state.remaining == 1
  | _ => false)

#guard pegFCakeParity

/-! Direct oracle for `seql_def` from
`cakeml/pancake/parser/panPEGScript.sml:115`.  Results concatenate in parser
order, the empty list supplies `[]`, and a failed component propagates. -/
def seqLCakeParity : Bool :=
  let input : PState := PState.ofToks [(.semiT, unknownLoc)]
  let success := P.seqL
      [P.pure' [1, 2], P.pure' [3], P.pure' []]
      (fun values => P.pure' values.length) input
  let empty : Option (List Nat) × PState := P.seqL []
      (fun values => P.pure' values) input
  let failing : P (List Nat) := fun state => (none, state)
  let failure := P.seqL [P.pure' [1], failing]
      (fun values => P.pure' values) input
  (match success with
  | (some 3, state) => state.toks == input.toks
  | _ => false) &&
  (match empty with
  | (some [], state) => state.toks == input.toks
  | _ => false) &&
  (match failure with
  | (none, state) => state.toks == input.toks
  | _ => false)

#guard seqLCakeParity

/-! Direct oracle for `try_def` from
`cakeml/pancake/parser/panPEGScript.sml:119`.  `P.tryRule` is Cake's
`choicel [s; empty []]`: successful input is retained, while failed input
backtracks and returns an empty child list. -/
def tryCakeParity : Bool :=
  let input : PState := PState.ofToks
    [(.keywordT .varK, unknownLoc), (.semiT, unknownLoc)]
  let success := P.tryRule (P.keepKw .varK "var") input
  let failure := P.tryRule (P.keepKw .funK "fun") input
  (match success with
  | (some [.lf (.keywordT .varK) _], state) => state.remaining == 1
  | _ => false) &&
  (match failure with
  | (some [], state) => state.remaining == 2 &&
      state.toks == input.toks && state.furthest.isSome
  | _ => false)

#guard tryCakeParity

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

/-! Direct oracle for `conv_binop_def` from
`cakeml/pancake/parser/panPtreeConversionScript.sml:125`.  Cake accepts a
single leaf below `AddOpsNT`, recursively converts the leaf, and rejects both
wrong node tags and every other child count. -/
def convBinopCakeParity : Bool :=
  convBinop (.lf (.plusT) unknownLoc) == some .add &&
  convBinop (.lf (.minusT) unknownLoc) == some .sub &&
  convBinop (.lf (.andT) unknownLoc) == some .and &&
  convBinop (.lf (.orT) unknownLoc) == some .or &&
  convBinop (.lf (.xorT) unknownLoc) == some .xor &&
  convBinop (.nd .addOps [(.lf (.plusT) unknownLoc)] unknownLoc) == some .add &&
  convBinop (.nd .addOps [] unknownLoc) == none &&
  convBinop (.nd .addOps
    [(.lf (.plusT) unknownLoc), (.lf (.minusT) unknownLoc)] unknownLoc) == none &&
  convBinop (.nd .mulOps [(.lf (.plusT) unknownLoc)] unknownLoc) == none

#guard convBinopCakeParity

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

-- Cake's catch-all localisation leaves this ld32 operand global, so a name
-- that exists only as a local is rejected by the static checker just as in
-- the original Pancake compiler (GH #1126).
#guard match parseTopDecs ofI "fun 1 f() {\n  var 1 z = 7;\n  var 1 y = ld32 z;\n  return y;\n}" with
  | .ok declarations => !staticResultOk (staticCheck declarations)
  | .error _ => false

-- Parsed declarations compile through `compileToCrep`, producing one
-- compiled function per source function.
#guard match parseTopDecs (BitVec.ofInt 64)
    "fun 1 f(1 a) { return a + 1; }\nfun 1 main() { var 1 r = f(2); return r; }" with
  | .ok declarations =>
      (compileToCrep
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
