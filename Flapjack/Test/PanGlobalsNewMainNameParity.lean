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

/-! Counterpart of Cake's `new_main_name_correct`
    (`pan_globalsProofScript.sml:2073`) and `fresh_name_correct` (`:993`). -/
example : True := by
  have h := globalNewMainName_not_mem
    [functionDecl "main", functionDecl "main'"]
  trivial

example : True := by
  have h := globalFreshName_not_mem "worker" ["worker", "worker'"]
  trivial

def correctnessGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [functionDecl "main", functionDecl "main'", functionDecl "worker"]
  !(globalFunctionNames declarations).contains
    (globalNewMainName declarations)

#eval correctnessGuard
#guard correctnessGuard

end Flapjack.Test.PanGlobalsNewMainNameParity
