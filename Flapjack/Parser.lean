import Flapjack.Parser.Conversion
import Flapjack.Parser.Localise

/-!
The public parser API.

`parseTopDecs` is the counterpart of `parse_topdecs_to_ast`: lex, run the
`panPEG` grammar to a parse tree, convert that tree with `panPtreeConversion`,
then run the localisation pass. `parseProgram` is the counterpart of
`parse_to_ast`, for a single statement sequence.

Both report a list of errors rather than `NONE`. Lexical errors are reported
together, as upstream's `safe_pancake_lex` does; a parse error is reported
singly, taken from the alternative that consumed the most input, which is
almost always the one the author meant.

`add_locs_annot` is available but off by default. Upstream emits it
unconditionally, wrapping every statement in
`Seq (Annot "location" "(r:c r:c)") _`, which roughly doubles the tree and
makes every AST comparison awkward. Pass `locations := true` to reproduce
upstream's output.
-/

namespace Flapjack.Parser

open Flapjack

/-- Turn a lexical error into the same shape as a parse error. -/
def lexErrorToParseError (entry : String × Locs) : ParseError :=
  { message := entry.1, locs := entry.2 }

/-- Run a grammar rule over a token list, requiring that it consumes
everything and yields exactly one tree. -/
def runGrammar (rule : Nat → P P.Trees) (toks : Toks) : Except ParseError ParseTree :=
  let state : PState := PState.ofToks toks
  match rule (parseFuel toks.length) state with
  | (some [tree], final) =>
      if final.toks.isEmpty then .ok tree
      else
        let locs := match final.toks with
          | [] => unknownLoc
          | (_, locs) :: _ => locs
        .error (final.furthest.getD { message := "Unexpected trailing input", locs := locs })
  | (some _, final) =>
      .error (final.furthest.getD
        { message := "The grammar produced no single tree", locs := unknownLoc })
  | (none, final) =>
      .error (final.furthest.getD { message := "Failed to parse", locs := unknownLoc })

/-- The error reported when the grammar succeeded but the conversion did not.
Upstream's `parse_topdecs_to_ast` reports the same case. -/
def conversionFailed : ParseError :=
  { message := "Parse tree conversion failed", locs := unknownLoc }

/--
`parse_topdecs_to_ast`: Pancake source to Flapjack declarations, with
variables classified as local or global.
-/
def parseTopDecs (ofInt : Int → α) (source : String) (locations : Bool := false) :
    Except (List ParseError) (List (Decl α)) :=
  match safePancakeLex source with
  | .error errors => .error (errors.map lexErrorToParseError)
  | .ok toks =>
      match runGrammar gTopDecList toks with
      | .error error => .error [error]
      | .ok tree =>
          match convTopDecList ofInt locations (parseFuel toks.length) tree with
          | none => .error [conversionFailed]
          | some declarations => .ok (localiseDecls declarations)

/--
`parse_to_ast`: a single statement sequence, as used for testing fragments.

Two differences from upstream's `parse_statement`. It expects the sequence to
be closed by `}`, whereas this accepts an unterminated one so a fragment need
not carry a stray brace. And `parse_to_ast` does not localise, since it is
only ever applied to a fragment with no enclosing function; here the pass runs
from an empty scope, so a variable declared inside the fragment comes back
`Local` rather than `Global`, which is what the same text would give inside a
function.
-/
def parseProgram (ofInt : Int → α) (source : String) (locations : Bool := false) :
    Except (List ParseError) (Prog α) :=
  match safePancakeLex source with
  | .error errors => .error (errors.map lexErrorToParseError)
  | .ok toks =>
      -- The synthetic closer inherits the last real token's end, so a range
      -- reaching it does not report `UNKNOWN`.
      let closer := match toks.getLast? with
        | none => unknownLoc
        | some (_, locs) => { start := locs.stop, stop := locs.stop }
      let closed := toks ++ [(Token.rCurT, closer)]
      match runGrammar gTryProg closed with
      | .error error => .error [error]
      | .ok tree =>
          match convProg ofInt locations (parseFuel closed.length) tree with
          | none => .error [conversionFailed]
          | some program => .ok (localiseProg [] program)

/-- Render an error for a human: `1:5: Failed to see expected token: ;`. -/
def formatError (error : ParseError) : String :=
  s!"{posnString error.locs.start}: {error.message}"

def formatErrors (errors : List ParseError) : String :=
  String.intercalate "\n" (errors.map formatError)

end Flapjack.Parser
