import Flapjack.PanGlobals

namespace Flapjack.Test.PanGlobalsNewMainNameParity

/-! Direct parity for `pan_globals$new_main_name_def`
    (`pan_globalsScript.sml:224`). -/
def functionDecl (name : FunName) : Decl Nat :=
  .function
    { name := name
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def parityGuard : Bool :=
  globalNewMainName ([] : List (Decl Nat)) == "main" &&
  globalNewMainName [functionDecl "main", functionDecl "main'"] == "main''" &&
  globalNewMainName
    [.decl .one "g" (.const 7), .name "S" [], .exnDecl "E" .one,
     functionDecl "main"] == "main'" &&
  globalNewMainName [functionDecl "worker"] == "main"

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanGlobalsNewMainNameParity
