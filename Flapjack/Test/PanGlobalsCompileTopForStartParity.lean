import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileTopForStartParity

def mainFunction : Decl Nat :=
  .function
    { name := "main"
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def parityGuard : Bool :=
  let missing :=
    globalCompileTopForStart 4 id [mainFunction] "absent"
  let simple :=
    globalCompileTopForStart 4 id [mainFunction] "main"
  (match missing with
  | [] => true
  | _ => false) &&
  (match simple with
  | [.function entry, .function renamed] =>
      entry.name == "main" &&
      entry.inline == false && entry.exported == false &&
      entry.params.isEmpty &&
      (match entry.returnShape with
      | .one => true
      | _ => false) &&
      (match entry.body with
      | .seq .skip (.call none "main'" []) => true
      | _ => false) &&
      renamed.name == "main'" &&
      (match renamed.body with
      | .skip => true
      | _ => false)
  | _ => false)

#eval parityGuard
#guard parityGuard

def correctnessGuard : Bool :=
  (globalCompileTopForStart 4 id [mainFunction] "main").all
    (fun declaration => globalDeclIsFunction declaration ||
      globalDeclIsException declaration)

#eval correctnessGuard
#guard correctnessGuard

example :
    (globalCompileTopForStart 4 id [mainFunction] "main").all
      (fun declaration => globalDeclIsFunction declaration ||
        globalDeclIsException declaration) = true := by
  exact globalCompileTopForStart_all_function_or_exception 4 id
    [mainFunction] "main"

def exceptionDecl : Decl Nat :=
  .exnDecl "E" (.named "T")

def exceptionGuard : Bool :=
  let declarations := [exceptionDecl, mainFunction]
  (exceptionEntries (globalCompileTopForStart 4 id declarations "main")).length ==
    (exceptionEntries declarations).length

#eval exceptionGuard
#guard exceptionGuard

example : True := by
  cases hcompile : globalCompileTopForStartSome 4 id
      [exceptionDecl, mainFunction] "main" with
  | none => trivial
  | some compiled =>
      have h := globalCompileTopForStart_exceptionEntries 4 id
        [exceptionDecl, mainFunction] "main" compiled hcompile
      trivial

def otherFunction : Decl Nat :=
  .function
    { name := "worker"
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def namesNodupGuard : Bool :=
  match globalCompileTopForStart 4 id [mainFunction, otherFunction] "main" with
  | compiled =>
      ((functions compiled).map (fun entry => entry.1)).Nodup

#eval namesNodupGuard
#guard namesNodupGuard

example : True := by
  cases hcompile : globalCompileTopForStartSome 4 id
      [mainFunction, otherFunction] "main" with
  | none => trivial
  | some compiled =>
      have hnodup : ((functions [mainFunction, otherFunction]).map
          (fun entry => entry.1)).Nodup := by
        decide
      have h := globalCompileTopForStart_names_nodup 4 id
        [mainFunction, otherFunction] "main" compiled hcompile hnodup
      trivial

end Flapjack.Test.PanGlobalsCompileTopForStartParity
