import Flapjack.Parser

namespace Flapjack.Test.ParserParseStatementParity

open Flapjack Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:475`, `parse_statement_def`.
    The public Lean wrapper closes a statement fragment with a synthetic brace,
    matching the closed token stream expected by the source parser. -/
def skipGuard : Bool :=
  match Parser.parseProgram (fun value => value) "skip;" with
  | .ok .skip => true
  | _ => false

def returnGuard : Bool :=
  match Parser.parseProgram (fun value => value) "return 1;" with
  | .ok (.return (.const 1)) => true
  | _ => false

#eval skipGuard && returnGuard
#guard skipGuard
#guard returnGuard

end Flapjack.Test.ParserParseStatementParity
