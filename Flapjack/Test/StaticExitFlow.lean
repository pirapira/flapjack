import Flapjack.Parser
import Flapjack.Static

/-! Acceptance tests for the static-checker exit-flow and tail-call checks
    (`panStaticScript.sml:1425-1459` and `:1324-1352`): code after a
    function exit is still checked (it only earns an unreachable-code
    warning), and a tail call requires the callee's return shape to match
    the caller's.  The verdicts mirror the CakeML `panStatic` rejection
    examples of GH #1042. -/

namespace Flapjack.Test.StaticExitFlow

open Flapjack Flapjack.Parser

abbrev ofI : Int → Int := fun value => value

def accepted (source : String) : Bool :=
  match (parseTopDecs ofI source).toOption with
  | none => false
  | some declarations => staticResultOk (staticCheck (α := Int) declarations)

def rejectedWith (kind : String) (source : String) : Bool :=
  match (parseTopDecs ofI source).toOption with
  | none => false
  | some declarations =>
      match staticCheck (α := Int) declarations with
      | (Except.error error, _) =>
          match error, kind with
          | .scope _, "scope" => true
          | .shape _, "shape" => true
          | .general _, "general" => true
          | _, _ => false
      | _ => false

/- A shape error after `return` still rejects the program. -/
#guard rejectedWith "shape" "\n  fun 1 main () {\n    return 0;\n    return <1,2>;\n  }\n"

/- A scope error after `return` still rejects the program. -/
#guard rejectedWith "scope" "\n  fun 1 f () {\n    return 0;\n    y = 1;\n  }\n"

/- A tail call whose callee return shape differs from the caller's is a
    shape error. -/
#guard rejectedWith "shape" "\n  fun {1,1} g () {\n    return <1,2>;\n  }\n  fun 1 main () {\n    return g();\n  }\n"

/- Matching tail-call shapes are accepted. -/
#guard accepted "\n  fun 1 g () {\n    return 1;\n  }\n  fun 1 main () {\n    return g();\n  }\n"

/- Unreachable code without further errors is only a warning. -/
#guard accepted "\n  fun 1 main () {\n    return 0;\n    return 1;\n  }\n"

end Flapjack.Test.StaticExitFlow
