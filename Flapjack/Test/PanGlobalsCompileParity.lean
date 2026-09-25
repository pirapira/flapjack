import Flapjack.Pancake.PanGlobals

namespace Flapjack.Test.PanGlobalsCompileParity

def compileContext : GlobalPassContext Nat :=
  { globals := [("g", (.one, 8))]
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

/-- Canonical 8-bit Cake context for exercising the canonical `compileProgCake`
    analogue directly against `pan_globals_compile_probe.out`. -/
def compileProgCakeContext8 : CakeContext 8 where
  globals := fun name =>
    if name == "g" then some (.one, BitVec.ofNat 8 8) else none
  globalsSize := BitVec.ofNat 8 1
  maxGlobalsSize := BitVec.ofNat 8 16

/-! These rows exercise `compileProgCake` itself, rather than only the
production `globalCompileProg` path. They mirror the direct HOL-EVAL rows in
`pan_globals_compile_probe.out`; the remaining carrier mismatch is recorded
beside the declaration and in the theorem map. -/
def compileProgCakeOracleGuard : Bool :=
  (match compileProgCake compileProgCakeContext8
      (.assign .local "x" (.const (BitVec.ofNat 8 7)) : Prog (BitVec 8)) with
  | .assign .local "x" (.const value) => value == BitVec.ofNat 8 7
  | _ => false) &&
  (match compileProgCake compileProgCakeContext8
      (.assign .global "g" (.const (BitVec.ofNat 8 7)) : Prog (BitVec 8)) with
  | .store (.op .sub [.topAddr, .const address]) (.const value) =>
      address == BitVec.ofNat 8 8 && value == BitVec.ofNat 8 7
  | _ => false) &&
  (match compileProgCake compileProgCakeContext8
      (.assign .global "missing" (.const (BitVec.ofNat 8 7)) : Prog (BitVec 8)) with
  | .skip => true
  | _ => false) &&
  (match compileProgCake compileProgCakeContext8
      (.seq .skip (.return (.const (BitVec.ofNat 8 7))) : Prog (BitVec 8)) with
  | .seq .skip (.return (.const value)) => value == BitVec.ofNat 8 7
  | _ => false) &&
  (match compileProgCake compileProgCakeContext8
      (.return (.var .global "g") : Prog (BitVec 8)) with
  | .return (.load .one (.op .sub [.topAddr, .const address])) =>
      address == BitVec.ofNat 8 8
  | _ => false) &&
  (match compileProgCake compileProgCakeContext8
      (.call (some (some (.global, "g"), some ("E", "handler", .skip))) "f" []
        : Prog (BitVec 8)) with
  | .dec "" .one (.const zero)
      (.dec "vn'" .one (.const flagZero)
        (.seq
          (.call
            (some (some (.local, ""), some ("E", "handler",
              .seq .skip (.assign .local "vn'" (.const flagOne)))))
            "f" [])
          (.ite (.var .local "vn'") .skip
            (.store (.op .sub [.topAddr, .const address])
              (.var .local ""))))) =>
      zero == BitVec.ofNat 8 0 && flagZero == BitVec.ofNat 8 0 &&
        flagOne == BitVec.ofNat 8 1 && address == BitVec.ofNat 8 8
  | _ => false)

#eval compileProgCakeOracleGuard
#guard compileProgCakeOracleGuard

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

/-! In Cake's global-destination handled-call branch, the result slot is
    freshened from `""`, but the handler flag is independently freshened from
    the fixed seed `"vn'"`. This direct generated-program regression matches
    `global_destination_handler_flag` in
    `scripts/hol-probes/pan_globals_compile_probe.out`. -/
def globalHandlerFlagInput : Prog Nat :=
  .call (some (some (.global, "g"), some ("E", "handler", .skip))) "f" []

def globalHandlerFlagGuard : Bool :=
  match globalCompileProg compileContext globalHandlerFlagInput with
  | .dec "" .one (.const 0)
      (.dec "vn'" .one (.const 0)
        (.seq
          (.call
            (some (some (.local, ""), some ("E", "handler",
              .seq .skip (.assign .local "vn'" (.const 1)))))
            "f" [])
          (.ite (.var .local "vn'") .skip
            (.store (.op .sub [.topAddr, .const 8]) (.var .local ""))))) => true
  | _ => false

#eval globalHandlerFlagGuard
#guard globalHandlerFlagGuard

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

/-! Cake compiles each global initializer with only the declarations that
    precede it in source order.  A reference to a later global therefore
    takes `compile_exp`'s zero fallback, even though the final global context
    used for function bodies contains that later declaration.  This guard is
    the direct source-shaped regression for GH #1063 and mirrors
    `pan_globalsScript.sml:162-169`. -/
def laterGlobalInitializerDecls : List (Decl Nat) :=
  [.decl .one "first" (.var .global "later"),
   .decl .one "later" (.const 7),
   .function
     { name := "main"
       inline := false
       exported := false
       params := []
       body := .return (.var .global "later")
       returnShape := .one }]

def precedingGlobalContextGuard : Bool :=
  let compiled := globalCompileTop 8 id laterGlobalInitializerDecls
  match compiled.initializers with
  | [.store (.op .sub [.topAddr, .const 8]) (.const 0),
     .store (.op .sub [.topAddr, .const 16]) (.const 7)] => true
  | _ => false

#guard precedingGlobalContextGuard

end Flapjack.Test.PanGlobalsCompileParity
