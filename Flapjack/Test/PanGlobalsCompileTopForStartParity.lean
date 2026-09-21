import Flapjack.PanGlobals

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
  | none => true
  | _ => false) &&
  (match simple with
  | some [.function entry, .function renamed] =>
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
  match globalCompileTopForStart 4 id [mainFunction] "main" with
  | some compiled =>
      compiled.all
        (fun declaration => globalDeclIsFunction declaration ||
          globalDeclIsException declaration)
  | none => false

#eval correctnessGuard
#guard correctnessGuard

example : True := by
  cases hcompile : globalCompileTopForStart 4 id [mainFunction] "main" with
  | none => trivial
  | some compiled =>
      have h := globalCompileTopForStart_all_function_or_exception 4 id
        [mainFunction] "main" compiled hcompile
      trivial

def exceptionDecl : Decl Nat :=
  .exnDecl "E" (.named "T")

def exceptionGuard : Bool :=
  let declarations := [exceptionDecl, mainFunction]
  match globalCompileTopForStart 4 id declarations "main" with
  | some compiled =>
      (exceptionEntries compiled).length ==
        (exceptionEntries declarations).length
  | none => false

#eval exceptionGuard
#guard exceptionGuard

example : True := by
  cases hcompile : globalCompileTopForStart 4 id
      [exceptionDecl, mainFunction] "main" with
  | none => trivial
  | some compiled =>
      have h := globalCompileTopForStart_exceptionEntries 4 id
        [exceptionDecl, mainFunction] "main" compiled hcompile
      trivial

end Flapjack.Test.PanGlobalsCompileTopForStartParity
