import Flapjack.Parser.Lexer

/-!
Parser state and combinators.

Upstream runs a PEG (`panPEG`) over the token list and then converts the
resulting parse tree (`panPtreeConversion`). This port keeps the grammar and
its ordered choices but drops the intermediate parse tree: each nonterminal is
one Lean function that returns the AST fragment directly. Rule names are kept,
so `panPEG`'s `EShiftNT` is `parseEShift` here and the two can be read side by
side.

Failure is `none` rather than an exception so that ordered choice can
backtrack. The furthest failure seen is carried in the state, which is what
turns a dead end into a useful message: reporting the alternative that got
deepest is much more informative than reporting the last one tried.
-/

namespace Flapjack.Parser

/-- A parse failure: what was expected, and where. -/
structure ParseError where
  message : String
  locs : Locs
  deriving DecidableEq, Repr, Inhabited

abbrev Toks := List (Token × Locs)

/-- Rank a position so that two failures can be compared for depth. -/
def posnRank : Posn → Nat × Nat
  | .posn row col => (row, col)
  | .eofPt => (Nat.succ 0xffffffff, 0)
  | .unknownPt => (0, 0)

def posnLe (left right : Posn) : Bool :=
  let (leftRow, leftCol) := posnRank left
  let (rightRow, rightCol) := posnRank right
  leftRow < rightRow || (leftRow == rightRow && leftCol ≤ rightCol)

structure PState where
  toks : Toks
  /-- The deepest failure seen so far, used for the eventual error message. -/
  furthest : Option ParseError
  /-- Emit `add_locs_annot` location annotations. Off unless asked for. -/
  locations : Bool := false
  /-- The location of the last token consumed by the current parser scope. -/
  lastConsumed : Option Locs := none
  deriving Inhabited

/-- A backtracking parser: `none` is failure, and the state survives it. -/
def P (α : Type) : Type := PState → Option α × PState

namespace P

def pure' (a : α) : P α := fun s => (some a, s)

def bind' (p : P α) (f : α → P β) : P β := fun s =>
  match p s with
  | (some a, s') => f a s'
  | (none, s') => (none, s')

instance : Monad P where
  pure := pure'
  bind := bind'

/-- Record a failure, keeping whichever candidate reached furthest. -/
def fail (message : String) : P α := fun s =>
  let locs := match s.toks with
    | [] => { start := .eofPt, stop := .eofPt : Locs }
    | (_, locs) :: _ => locs
  let candidate : ParseError := { message := message, locs := locs }
  let furthest := match s.furthest with
    | none => some candidate
    | some existing =>
        if posnLe existing.locs.start candidate.locs.start then some candidate else some existing
  (none, { s with furthest := furthest })

/-- Ordered choice: take the first success, but keep the deepest failure. -/
def orElse' (p : P α) (q : P α) : P α := fun s =>
  match p s with
  | (some a, s') => (some a, s')
  | (none, s') => q { s' with toks := s.toks, lastConsumed := s.lastConsumed }

instance : OrElse (P α) where
  orElse p q := orElse' p (q ())

/-- Run a parser but treat failure as success with `none`, mirroring `try`. -/
def optional' (p : P α) : P (Option α) := fun s =>
  match p s with
  | (some a, s') => (some a, s')
  | (none, s') =>
      (some none, { s' with toks := s.toks, lastConsumed := s.lastConsumed })

def peek : P (Option Token) := fun s =>
  (some (s.toks.head?.map Prod.fst), s)

def currentLocs : P Locs := fun s =>
  let locs := match s.toks with
    | [] => { start := .eofPt, stop := .eofPt : Locs }
    | (_, locs) :: _ => locs
  (some locs, s)

def atEnd : P Bool := fun s => (some s.toks.isEmpty, s)

/-- Consume the next token, whatever it is. -/
def advance : P Token := fun s =>
  match s.toks with
  | [] => P.fail "Didn't expect an EOF" s
  | (token, locs) :: rest =>
      (some token, { s with toks := rest, lastConsumed := some locs })

/-- Consume a specific token, mirroring `consume_tok`. -/
def expect (expected : Token) (described : String) : P Unit := fun s =>
  match s.toks with
  | (token, locs) :: rest =>
      if token == expected then
        (some (), { s with toks := rest, lastConsumed := some locs })
      else P.fail s!"Failed to see expected token: {described}" s
  | [] => P.fail s!"Failed to see expected token; saw EOF instead: {described}" s

/-- Consume a specific keyword, mirroring `consume_kw`. -/
def expectKw (keyword : Keyword) (described : String) : P Unit :=
  expect (.keywordT keyword) described

/-- Consume an identifier, mirroring `keep_ident` followed by `conv_ident`. -/
def ident : P String := fun s =>
  match s.toks with
  | (.identT name, locs) :: rest =>
      (some name, { s with toks := rest, lastConsumed := some locs })
  | _ => P.fail "Expected an identifier" s

/-- Consume an `@name` foreign identifier, mirroring `keep_ffi_ident`. -/
def ffiIdent : P String := fun s =>
  match s.toks with
  | (.foreignIdent name, locs) :: rest =>
      (some name, { s with toks := rest, lastConsumed := some locs })
  | _ => P.fail "Expected a foreign identifier" s

/-- Consume an integer literal, mirroring `keep_int`. -/
def intLit : P Int := fun s =>
  match s.toks with
  | (.intT value, locs) :: rest =>
      (some value, { s with toks := rest, lastConsumed := some locs })
  | _ => P.fail "Expected an integer literal" s

/-- Consume a non-negative integer literal, mirroring `keep_nat`/`conv_nat`. -/
def natLit : P Nat := fun s =>
  match s.toks with
  | (.intT value, locs) :: rest =>
      if 0 ≤ value then
        (some value.toNat, { s with toks := rest, lastConsumed := some locs })
      else P.fail "Expected a non-negative integer literal" s
  | _ => P.fail "Expected a non-negative integer literal" s

/-- Consume an annotation comment, mirroring `keep_annot`. -/
def annotLit : P String := fun s =>
  match s.toks with
  | (.annotCommentT text, locs) :: rest =>
      (some text, { s with toks := rest, lastConsumed := some locs })
  | _ => P.fail "Expected an annotation comment" s

/-- Collect `, item` repetitions. Each accepted separator consumes a token, so
recursion on the remaining token count terminates. -/
def commaTail (item : P α) : Nat → P (List α)
  | 0 => pure []
  | fuel + 1 => do
      match ← optional' (expect .commaT ",") with
      | none => pure []
      | some _ =>
          let next ← item
          let rest ← commaTail item fuel
          pure (next :: rest)

/-- Parse one or more `item` separated by commas, mirroring the
`rpt (seql [consume_tok CommaT; ...])` shape used throughout `panPEG`. -/
def sepByComma (item : P α) : P (List α) := fun s => (do
    let first ← item
    let rest ← commaTail item s.toks.length
    pure (first :: rest)) s

/-- Run a parser and report the source range it consumed. Upstream reads this
off the parse-tree node's `locs`; here it comes from the tokens consumed. -/
def spanned (p : P α) : P (α × Locs) := fun s =>
  match p { s with lastConsumed := none } with
  | (some value, s') =>
      let start := match s.toks with
        | [] => Posn.eofPt
        | (_, locs) :: _ => locs.start
      let stop := match s'.lastConsumed with
        | none => start
        | some locs => locs.stop
      let finalState := match s'.lastConsumed with
        | none => { s' with lastConsumed := s.lastConsumed }
        | some _ => s'
      (some (value, { start := start, stop := stop }), finalState)
  | (none, s') => (none, s')

end P

end Flapjack.Parser
