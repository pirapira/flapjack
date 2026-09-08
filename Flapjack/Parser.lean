import Flapjack.Parser.Statements
import Flapjack.Parser.Localise

/-!
The public parser API.

`parseTopDecs` is the counterpart of `parse_topdecs_to_ast`: lex, parse the
top-level declarations, then run the localisation pass. `parseProgram` is the
counterpart of `parse_to_ast`, for a single statement sequence.

Both report a list of errors rather than `NONE`. Lexical errors are reported
together, as upstream's `safe_pancake_lex` does; a parse error is reported
singly, taken from the alternative that consumed the most input, which is
almost always the one the author meant.

`add_locs_annot` is available but off by default. Upstream emits it
unconditionally, wrapping every statement in
`Seq (Annot "location" "(r:c r:c)") _`, which roughly doubles the tree and
makes every AST comparison awkward. Pass `locations := true` to reproduce
upstream's output; the structured errors here are what covers diagnostics
otherwise.
-/

namespace Flapjack.Parser

open Flapjack

/-- `FunNT`: `[inline] [export] fun <shape> name(params) { body }`. -/
def parseFun (ofInt : Int → α) (fuel : Nat) : P (FunDecl α) := do
  let inline ← P.optional' (P.expectKw .inlineK "inline")
  let exported ← P.optional' (P.expectKw .exportK "export")
  P.expectKw .funK "fun"
  let (name, returnShape) ← parseShapedIdent fuel
  P.expect .lParT "("
  let params ← P.optional' (parseParamList fuel)
  P.expect .rParT ")"
  P.expect .lCurT "{"
  let body ← parseTryProg ofInt fuel
  pure { name := name
         inline := inline.isSome
         exported := exported.isSome
         params := params.getD []
         body := body
         returnShape := returnShape }

/--
One top-level item. `none` is an annotation comment, which `conv_TopDecList`
drops rather than turning into a declaration.
-/
def parseTopDec (ofInt : Int → α) (fuel : Nat) : P (Option (Decl α)) :=
  (do
    let declaration ← parseFun ofInt fuel
    pure (some (.function declaration)))
  <|> (do
    let (name, shape, value) ← parseDecBody ofInt fuel
    pure (some (.decl shape name value)))
  <|> (do
    let (exception, shape) ← parseExnDec fuel
    pure (some (.exnDecl exception shape)))
  <|> (do
    let (name, fields) ← parseStructName fuel
    pure (some (.name name fields)))
  <|> (do
    let _ ← P.annotLit
    pure none)

/-- `TopDecListNT`: items until end of input. -/
def parseTopDecList (ofInt : Int → α) (fuel : Nat) : Nat → P (List (Decl α))
  | 0 => P.fail fuelExhausted
  | steps + 1 => do
      if ← P.atEnd then
        pure []
      else
        let item ← parseTopDec ofInt fuel
        let rest ← parseTopDecList ofInt fuel steps
        pure (match item with
          | none => rest
          | some declaration => declaration :: rest)

/-- Run a parser over a token list, requiring that it consumes everything. -/
def runParser (parser : Nat → P α) (toks : Toks) (locations : Bool := false) :
    Except ParseError α :=
  let state : PState := { toks := toks, furthest := none, locations := locations }
  match parser (parseFuel toks.length) state with
  | (some value, final) =>
      if final.toks.isEmpty then .ok value
      else
        let locs := match final.toks with
          | [] => unknownLoc
          | (_, locs) :: _ => locs
        .error (final.furthest.getD { message := "Unexpected trailing input", locs := locs })
  | (none, final) =>
      .error (final.furthest.getD { message := "Failed to parse", locs := unknownLoc })

/-- Turn a lexical error into the same shape as a parse error. -/
def lexErrorToParseError (entry : String × Locs) : ParseError :=
  { message := entry.1, locs := entry.2 }

/--
`parse_topdecs_to_ast`: Pancake source to Flapjack declarations, with
variables classified as local or global.
-/
def parseTopDecs (ofInt : Int → α) (source : String) (locations : Bool := false) :
    Except (List ParseError) (List (Decl α)) :=
  match safePancakeLex source with
  | .error errors => .error (errors.map lexErrorToParseError)
  | .ok toks =>
      match runParser (fun fuel => parseTopDecList ofInt fuel toks.length.succ)
          toks locations with
      | .error error => .error [error]
      | .ok declarations => .ok (localiseDecls declarations)

/--
`parse_to_ast`: a single statement sequence, as used for testing fragments.

Two differences from upstream's `parse_statement`. It expects the sequence to
be closed by `}`, whereas this accepts an unterminated one so a fragment need
not carry a stray brace. And `parse_to_ast` does not localise, since it is
only ever applied to a fragment with no enclosing function; here the pass runs
from an empty scope, so a variable declared inside the fragment comes back
`Local` rather than `Global`. That is what a caller of a fragment parser
wants, and it agrees with what the same text would give inside a function.
-/
def parseProgram (ofInt : Int → α) (source : String) (locations : Bool := false) :
    Except (List ParseError) (Prog α) :=
  match safePancakeLex source with
  | .error errors => .error (errors.map lexErrorToParseError)
  | .ok toks =>
      -- The synthetic closer inherits the last real token's end, so a span
      -- reaching it does not report `UNKNOWN`.
      let closer := match toks.getLast? with
        | none => unknownLoc
        | some (_, locs) => { start := locs.stop, stop := locs.stop }
      let closed := toks ++ [(Token.rCurT, closer)]
      match runParser (parseTryProg ofInt) closed locations with
      | .error error => .error [error]
      | .ok program => .ok (localiseProg [] program)

/-- Render an error for a human: `1:5: Failed to see expected token: ;`. -/
def formatError (error : ParseError) : String :=
  s!"{posnString error.locs.start}: {error.message}"

def formatErrors (errors : List ParseError) : String :=
  String.intercalate "\n" (errors.map formatError)

end Flapjack.Parser
