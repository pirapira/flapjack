/-!
A lexer for the Pancake language.

This is the Lean counterpart of CakeML's `panLexer` theory. Token and keyword
constructors keep their upstream names (`SkipK` becomes `skipK`, `LParT`
becomes `lParT`) so that the two can be read side by side.

Upstream recurses on the remaining input and discharges termination with a
`measure (LENGTH o FST)` relation. Here the recursion is structural on an
explicit fuel bound instead: every step consumes at least one character, so
seeding the fuel with the input length loses nothing, and it keeps the lexer
free of well-founded recursion.
-/

namespace Flapjack.Parser

/-- Encode a source string to the list of bytes the original CakeML lexer
    observes. HOL `string` is a `char list` with 256 possible characters, and the
    executed compiler reads the source file as bytes through CakeML's UTF-8 file
    input; re-encoding the Lean decoded string recovers exactly those bytes.
    This keeps accepted identifiers byte-valued, so `MlString.ofString`
    round-trips without silent truncation. -/
def utf8Bytes (s : String) : List Char :=
  s.toUTF8.toList.map (fun b => Char.ofNat b.toNat)

/-- Reserved words, mirroring `panLexer$keyword`. -/
inductive Keyword where
  | skipK | stK | stwK | st8K | st16K | st32K | ifK | elseK | whileK
  | brK | contK | throwK | retK | ticK | varK | tryK | catchK | biwK | namedK
  | ldsK | ld8K | ldwK | ld16K | ld32K | baseK | topK | inK | funK | exportK
  | trueK | falseK | inlineK | exceptionK
  deriving DecidableEq, Repr, Inhabited

/-- Tokens, mirroring `panLexer$token`. -/
inductive Token where
  | andT | orT | boolAndT | boolOrT | xorT | notT | arrowT
  | eqT | neqT | lessT | greaterT | geqT | leqT | lowerT | higherT | higheqT | loweqT
  | plusT | minusT | dotT | starT
  | lslT | lsrT | asrT | rorT
  | intT (value : Int)
  | identT (name : String)
  /-- `@ffi_str`, excluding `@base`, `@biw` and `@top`. -/
  | foreignIdent (name : String)
  | lParT | rParT | commaT | semiT | colonT | addrT
  | lBrakT | rBrakT | lCurT | rCurT
  | assignT
  | staticT
  | noinlineT
  | defaultShT
  | keywordT (keyword : Keyword)
  | annotCommentT (text : String)
  | lexErrorT (message : String)
  deriving DecidableEq, Repr, Inhabited

/-- Source positions, mirroring `locationTheory`'s `POSN`/`EOFpt`/`UNKNOWNpt`. -/
inductive Posn where
  | posn (row col : Nat)
  | eofPt
  | unknownPt
  deriving DecidableEq, Repr, Inhabited

/-- A start and end position, mirroring `Locs`. -/
structure Locs where
  start : Posn
  stop : Posn
  deriving DecidableEq, Repr, Inhabited

def unknownLoc : Locs := { start := .unknownPt, stop := .unknownPt }

/-- `posn_string`. -/
def posnString : Posn → String
  | .posn row col => s!"{row}:{col}"
  | .eofPt => "EOF"
  | .unknownPt => "UNKNOWN"

/-- `locs_comment`. -/
def locsComment (locs : Locs) : String :=
  s!"({posnString locs.start} {posnString locs.stop})"

/-- The tag `add_locs_annot` uses. -/
def locationTag : String := "location"

def initLoc : Posn := .posn 1 1

/-! Cake `loc_row`: a source row starts at column one. -/
def locRow (row : Nat) : Posn := .posn row 1

def nextLoc (n : Nat) : Posn → Posn
  | .posn row col => .posn row (col + n)
  | other => other

def nextLine : Posn → Posn
  | .posn row _ => .posn (row + 1) 0
  | other => other

/-- Intermediate lexemes, mirroring `panLexer$atom`. -/
inductive Atom where
  | numberA (value : Int)
  | wordA (text : String)
  | symA (text : String)
  | errA (message : String)
  | annotCommentA (text : String)
  deriving DecidableEq, Repr, Inhabited

def isAtomSingleton (c : Char) : Bool := "+-^*().,;:[]{}".toList.contains c

/-- `#` is only used by `#>>`; upstream notes it should eventually go, to avoid
colliding with the C preprocessor. -/
def isAtomBeginGroup (c : Char) : Bool := "#=><!&|".toList.contains c

def isAtomInGroup (c : Char) : Bool := "=<>|&+".toList.contains c

/-- ASCII range tests matching HOL `string$isDigit`/`isLower`/`isUpper`/`isAlpha`/`isAlphaNum`
    (`HOL/src/string/stringScript.sml:74-95`). The original Pancake lexer operates on
    `char list` where HOL `char` has exactly 256 values, so a byte >= 128 is neither a
    letter nor a digit; Lean's Unicode `Char.isAlpha`/`isDigit`/`isAlphanum` would wrongly
    accept such codepoints and later truncate them in `MlString.ofString`. -/
def isDigitAscii (c : Char) : Bool := decide (48 ≤ c.toNat ∧ c.toNat ≤ 57)

def isLowerAscii (c : Char) : Bool := decide (97 ≤ c.toNat ∧ c.toNat ≤ 122)

def isUpperAscii (c : Char) : Bool := decide (65 ≤ c.toNat ∧ c.toNat ≤ 90)

def isAlphaAscii (c : Char) : Bool := isLowerAscii c || isUpperAscii c

def isAlphaNumAscii (c : Char) : Bool := isAlphaAscii c || isDigitAscii c

/-- HOL `string$isSpace` (`stringScript.sml:95`): `ORD c = 32 \/ 9 <= ORD c /\ ORD c <= 13`. -/
def isSpaceAscii (c : Char) : Bool := decide (c.toNat = 32 ∨ (9 ≤ c.toNat ∧ c.toNat ≤ 13))

def isAlphaNumOrWild (c : Char) : Bool := isAlphaNumAscii c || c == '_'

/-- Every character the lexer admits into a digit is a byte below 128. -/
theorem isDigitAscii_lt128 {c : Char} (h : isDigitAscii c = true) : c.toNat < 128 := by
  simp only [isDigitAscii, decide_eq_true_eq] at h
  omega

/-- Every character the lexer admits into an identifier is a byte below 128. -/
theorem isAlphaNumOrWild_lt128 {c : Char} (h : isAlphaNumOrWild c = true) : c.toNat < 128 := by
  simp only [isAlphaNumOrWild, Bool.or_eq_true] at h
  rcases h with h | h
  · simp only [isAlphaNumAscii, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [isAlphaAscii, Bool.or_eq_true] at h
      rcases h with h | h
      · simp only [isLowerAscii, decide_eq_true_eq] at h; omega
      · simp only [isUpperAscii, decide_eq_true_eq] at h; omega
    · exact isDigitAscii_lt128 h
  · have : c = '_' := by simpa using h
    subst this
    decide

def isLexErrorT : Token → Bool
  | .lexErrorT _ => true
  | _ => false

def destLexErrorT : Token → Option String
  | .lexErrorT message => some message
  | _ => none

def getToken (s : String) : Token :=
  if s == "&&" then .boolAndT
  else if s == "||" then .boolOrT
  else if s == "&" then .andT
  else if s == "|" then .orT
  else if s == "^" then .xorT
  else if s == "==" then .eqT
  else if s == "=>" then .arrowT
  else if s == "!=" then .neqT
  else if s == "<" then .lessT
  else if s == ">" then .greaterT
  else if s == ">=" then .geqT
  else if s == "<=" then .leqT
  else if s == "<+" then .lowerT
  else if s == ">+" then .higherT
  else if s == ">=+" then .higheqT
  else if s == "<=+" then .loweqT
  else if s == "!" then .notT
  else if s == "+" then .plusT
  else if s == "-" then .minusT
  else if s == "*" then .starT
  else if s == "." then .dotT
  else if s == "<<" then .lslT
  else if s == ">>>" then .lsrT
  else if s == ">>" then .asrT
  else if s == "#>>" then .rorT
  else if s == "(" then .lParT
  else if s == ")" then .rParT
  else if s == "," then .commaT
  else if s == ";" then .semiT
  else if s == ":" then .colonT
  else if s == "[" then .lBrakT
  else if s == "]" then .rBrakT
  else if s == "{" then .lCurT
  else if s == "}" then .rCurT
  else if s == "=" then .assignT
  else .lexErrorT s!"Unrecognised symbolic token: {s}"

/--
Keyword lookup, mirroring `panLexer$get_keyword`. Cake maps both `@base` and
`@top` to `BaseK`; this intentionally preserves that source behavior.
-/
def getKeyword (s : String) : Token :=
  if s == "skip" then .keywordT .skipK
  else if s == "st" then .keywordT .stK
  else if s == "stw" then .keywordT .stwK
  else if s == "st8" then .keywordT .st8K
  else if s == "st16" then .keywordT .st16K
  else if s == "st32" then .keywordT .st32K
  else if s == "if" then .keywordT .ifK
  else if s == "else" then .keywordT .elseK
  else if s == "while" then .keywordT .whileK
  else if s == "break" then .keywordT .brK
  else if s == "continue" then .keywordT .contK
  else if s == "throw" then .keywordT .throwK
  else if s == "return" then .keywordT .retK
  else if s == "tick" then .keywordT .ticK
  else if s == "var" then .keywordT .varK
  else if s == "in" then .keywordT .inK
  else if s == "try" then .keywordT .tryK
  else if s == "catch" then .keywordT .catchK
  else if s == "lds" then .keywordT .ldsK
  else if s == "ldw" then .keywordT .ldwK
  else if s == "ld8" then .keywordT .ld8K
  else if s == "ld16" then .keywordT .ld16K
  else if s == "ld32" then .keywordT .ld32K
  else if s == "@base" then .keywordT .baseK
  else if s == "@top" then .keywordT .baseK
  else if s == "@biw" then .keywordT .biwK
  else if s == "true" then .keywordT .trueK
  else if s == "false" then .keywordT .falseK
  else if s == "fun" then .keywordT .funK
  else if s == "export" then .keywordT .exportK
  else if s == "inline" then .keywordT .inlineK
  else if s == "exception" then .keywordT .exceptionK
  else if s == "struct" then .keywordT .namedK
  else if s == "" then .lexErrorT "Expected keyword, found empty string"
  else if 2 ≤ s.length && s.front == '@' then .foreignIdent (String.ofList (s.toList.drop 1))
  else .identT s

def tokenOfAtom : Atom → Token
  | .numberA value => .intT value
  | .wordA text => getKeyword text
  | .symA text => getToken text
  | .errA message => .lexErrorT message
  | .annotCommentA text => .annotCommentT text

/-- `read_while`, returning the accepted prefix and the remaining input. -/
def readWhile (p : Char → Bool) : List Char → List Char → String × List Char
  | [], acc => (String.ofList acc.reverse, [])
  | c :: cs, acc => if p c then readWhile p cs (c :: acc) else (String.ofList acc.reverse, c :: cs)

theorem readWhile_length (p : Char → Bool) (input acc : List Char) :
    (readWhile p input acc).2.length ≤ input.length := by
  induction input generalizing acc with
  | nil => simp [readWhile]
  | cons c cs ih =>
      by_cases h : p c
      · simpa [readWhile, h] using Nat.le_succ_of_le (ih (c :: acc))
      · simp [readWhile, h]

/-- Skip a line comment, returning the position after it and its length. -/
def skipComment : List Char → Posn → Nat → Option (Posn × Nat)
  | [], _, _ => none
  | c :: cs, loc, i =>
      if c == '\n' then some (nextLine loc, i + 1)
      else skipComment cs (nextLoc 1 loc) (i + 1)

/--
Skip a block comment. Returns the position after it, the number of characters
inside it, and the number to drop to continue after the closing delimiter.
-/
def skipBlockComment : List Char → Posn → Nat → Option (Posn × Nat × Nat)
  | [], _, _ => none
  | [_], _, _ => none
  | x :: y :: xs, loc, i =>
      if (x == '*' && y == '/') || (x == '@' && y == '/') then
        some (nextLoc 2 loc, i, i + 2)
      else if x == '\n' then skipBlockComment (y :: xs) (nextLine loc) (i + 1)
      else skipBlockComment (y :: xs) (nextLoc 1 loc) (i + 1)

/--
Cake's `unhex_alt` (`panLexerScript.sml:217`).  Keep the helper total, as in
`UNHEX`: callers get zero for a non-hexadecimal character.
-/
def unhexAlt (c : Char) : Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then n - 48
  else if 97 ≤ n && n ≤ 102 then 10 + n - 97
  else if 65 ≤ n && n ≤ 70 then 10 + n - 65
  else 0

/-! Cake's `num_from_dec_string_alt_def` is `s2n 10 unhex_alt`.
    `l2n` over the reversed list is the same left-to-right accumulator. -/
def numFromDecStringAlt (s : String) : Nat :=
  s.toList.foldl (fun total c => total * 10 + unhexAlt c) 0

def numFromDecString (s : String) : Nat :=
  numFromDecStringAlt s

/--
`next_atom`: read one lexeme, skipping whitespace and comments.

`fuel` bounds only the whitespace- and comment-skipping recursion; each such
step consumes at least one character, so `input.length` always suffices.
-/
def nextAtom : Nat → List Char → Posn → Option (Atom × Locs × List Char)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, c :: cs, loc =>
      if c == '\n' then nextAtom fuel cs (nextLine loc)
      -- CakeML `isSpace` (`panLexerScript.sml:230`) is the ASCII test
      -- `ORD c = 32 \/ 9 <= ORD c /\ ORD c <= 13`.
      else if isSpaceAscii c then nextAtom fuel cs (nextLoc 1 loc)
      else if isDigitAscii c then
        let (n, cs') := readWhile isDigitAscii cs [c]
        some (.numberA (Int.ofNat (numFromDecStringAlt n)),
              { start := loc, stop := nextLoc n.length loc }, cs')
      else if c == '-' && (cs.head?.map isDigitAscii).getD false then
        let (n, rest) := readWhile isDigitAscii cs []
        some (.numberA (0 - Int.ofNat (numFromDecStringAlt n)),
              { start := loc, stop := nextLoc n.length loc }, rest)
      else if c == '/' && cs.head? == some '/' then
        match skipComment cs.tail (nextLoc 2 loc) 0 with
        | none => some (.errA "Malformed comment", { start := loc, stop := nextLoc 2 loc }, [])
        | some (loc', len) => nextAtom fuel (cs.drop (len + 1)) loc'
      else if c == '/' && cs.head? == some '@' then
        match skipBlockComment cs.tail (nextLoc 3 loc) 0 with
        | none => some (.errA "Malformed comment", { start := loc, stop := nextLoc 3 loc }, [])
        | some (loc', i, len) =>
            some (.annotCommentA (String.ofList (cs.tail.take i)),
                  { start := loc, stop := loc' }, cs.drop (len + 1))
      else if c == '/' && cs.head? == some '*' then
        match skipBlockComment cs.tail (nextLoc 2 loc) 0 with
        | none => some (.errA "Malformed comment", { start := loc, stop := nextLoc 2 loc }, [])
        | some (loc', _, len) => nextAtom fuel (cs.drop (len + 1)) loc'
      else if isAtomSingleton c then
        some (.symA (String.ofList [c]), { start := loc, stop := loc }, cs)
      else if isAtomBeginGroup c then
        let (n, rest) := readWhile isAtomInGroup cs [c]
        some (.symA n, { start := loc, stop := nextLoc (n.length - 1) loc }, rest)
      else if isAlphaAscii c || c == '@' || c == '_' then
        let (n, rest) := readWhile isAlphaNumOrWild cs [c]
        some (.wordA n, { start := loc, stop := nextLoc n.length loc }, rest)
      else
        some (.errA s!"Unrecognised symbol: {c}", { start := loc, stop := loc }, cs)

def nextToken (fuel : Nat) (input : List Char) (loc : Posn) :
    Option (Token × Locs × List Char) :=
  match nextAtom fuel input loc with
  | none => none
  | some (atom, locs, rest) => some (tokenOfAtom atom, locs, rest)

/-- `pancake_lex_aux`, with the same fuel treatment as `nextAtom`. -/
def lexAux : Nat → List Char → Posn → List (Token × Locs)
  | 0, _, _ => []
  | fuel + 1, input, loc =>
      match nextToken (fuel + 1) input loc with
      | none => []
      | some (token, locs, rest) => (token, locs) :: lexAux fuel rest locs.stop

/-- Lex Pancake source into tokens paired with their source ranges. -/
def pancakeLex (input : String) : List (Token × Locs) :=
  let chars := utf8Bytes input
  lexAux (chars.length + 1) chars initLoc

/--
`safe_pancake_lex`: lex, and report every lexical error instead of leaving
error tokens in the stream for the parser to trip over.
-/
def safePancakeLex (input : String) : Except (List (String × Locs)) (List (Token × Locs)) :=
  let output := pancakeLex input
  match output.filter (fun tokenLocs => isLexErrorT tokenLocs.1) with
  | [] => .ok output
  | errors => .error (errors.map fun (token, locs) => ((destLexErrorT token).getD "", locs))

end Flapjack.Parser
