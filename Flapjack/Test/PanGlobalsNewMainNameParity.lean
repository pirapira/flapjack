import Flapjack.Pancake.PanGlobals

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

/-! Counterpart of Cake's `fresh_name_correct'`
    (`pan_globalsProofScript.sml:1003`). -/
example : True := by
  have h := globalFreshName_not_mem_of_subset "worker" ["worker", "worker'"]
    (names' := ["worker"]) (fun candidate hmem => by
      simp at hmem ⊢
      exact Or.inl hmem)
  trivial

def subsetCorrectnessGuard : Bool :=
  let names : List String := ["worker", "worker'"]
  let names' : List String := ["worker"]
  !names'.contains (globalFreshName "worker" names)

#eval subsetCorrectnessGuard
#guard subsetCorrectnessGuard

end Flapjack.Test.PanGlobalsNewMainNameParity
