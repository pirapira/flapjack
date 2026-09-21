import Flapjack.Parser

/-! Direct source-shaped coverage for
    `cakeml/pancake/parser/panPEGScript.sml:482`, `parse_def`.

Cake returns `INL` for one fully consumed converted top-declaration tree and
`INR` for trailing-token or parse failures.  `Parser.parseDef` exposes the
same two branches while retaining the existing compiler-facing `Except` API.
-/

namespace Flapjack.Test.ParserParseDefParity

open Flapjack Flapjack.Parser

def sameAst {α : Type} [Repr α] (actual expected : α) : Bool :=
  reprStr actual == reprStr expected

def valid : Bool :=
  match Flapjack.Parser.parseDef (fun value => value) "fun f() { skip; }" with
  | .inl declarations => declarations.length == 1
  | _ => false

def trailing : Bool :=
  match Flapjack.Parser.parseDef (fun value => value) "fun f() { skip; };" with
  | .inr errors => !errors.isEmpty
  | _ => false

def malformed : Bool :=
  match Flapjack.Parser.parseDef (fun value => value) "fun f() {" with
  | .inr errors => !errors.isEmpty
  | _ => false

#guard valid
#guard trailing
#guard malformed

end Flapjack.Test.ParserParseDefParity
