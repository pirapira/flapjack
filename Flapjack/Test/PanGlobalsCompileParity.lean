import Flapjack.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileParity

def compileContext : GlobalPassContext Nat :=
  { globals := [("g", (.one, 8))]
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

/-! Direct parity for `pan_globals$compile_def`
    (`pan_globalsScript.sml:69`). -/
def parityGuard : Bool :=
  (match globalCompileProg compileContext
      (.assign .local "x" (.const 7)) with
  | .assign .local "x" (.const 7) => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.assign .global "g" (.const 7)) with
  | .store (.op .sub [.topAddr, .const 8]) (.const 7) => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.assign .global "missing" (.const 7)) with
  | .skip => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.seq .skip (.return (.const 7))) with
  | .seq .skip (.return (.const 7)) => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.return (.var .global "g")) with
  | .return (.load .one (.op .sub [.topAddr, .const 8])) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

/-! Cake's duplicate top-level declarations retain one initializer per
    declaration, while the final `FLOOKUP` binding is the last declaration.
    This is the source-level contract exercised by
    `Flapjack/Test/OriginalPancake/dup_global.pnk`; the warning is handled by
    the static checker, and this guard pins the address/layout semantics before
    the later allocator boundary. -/
def duplicateGlobalDecls : List (Decl Nat) :=
  [.decl .one "g" (.const 7),
   .decl .one "g" (.const 7),
   .function
     { name := "main"
       inline := false
       exported := false
       params := []
       body := .return (.var .global "g")
       returnShape := .one }]

def duplicateGlobalLayoutGuard : Bool :=
  let compiled := globalCompileTop 8 id duplicateGlobalDecls
  match compiled.initializers, compiled.declarations with
  | [.store (.op .sub [.topAddr, .const 8]) (.const 7),
     .store (.op .sub [.topAddr, .const 16]) (.const 7)],
    [.function declaration] =>
      match declaration.body with
      | .return (.load .one (.op .sub [.topAddr, .const 16])) => true
      | _ => false
  | _, _ => false

#guard duplicateGlobalLayoutGuard

end Flapjack.Test.PanGlobalsCompileParity
