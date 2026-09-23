import Flapjack.Pipeline
import Flapjack.Pancake.PanToCrep.Compile

namespace Flapjack.Test.DupExnEidsParity

open Flapjack

/-! Direct executable-boundary parity for repeated exception declarations.

The oracle is `scripts/hol-probes/dup_exn_eids_probe.out`, regenerated from
`pan_to_crep$get_eids_from_decls` and `pan_to_crep$compile_to_crep`
(`cakeml/pancake/pan_to_crepScript.sml:356-391`) by
`scripts/hol-probes/dup_exn_eids_probeScript.sml`.

`get_eids_from_decls` numbers every exception declaration in source order and
folds the pairs with `alist_to_fmap`, whose evaluation returns the *first*
binding for a repeated key.  (This differs from `make_vmap`, which uses
`FEMPTY |++` and keeps the later binding.)  A repeated exception name therefore
resolves to the ID of its first declaration.  Flapjack's list-backed
`InfoMap`/`lookupInfo` is also first-binding, so no executable divergence is
present; these checks pin that agreement. -/

/-- Source-shaped exception declarations with a repeated name. -/
def dupExnDecls : List (Decl Nat) :=
  [.exnDecl "E" .one, .exnDecl "E" .one]

/-- A distinct name followed by a repeated one. -/
def mixedExnDecls : List (Decl Nat) :=
  [.exnDecl "A" .one, .exnDecl "E" .one, .exnDecl "E" .one]

/-- Flapjack keeps the intermediate table in source order, one entry per
declaration; the later duplicate entry is shadowed by `lookupInfo`. -/
theorem dup_exn_eids_table :
    crepGetEidsFromDecls (fun index => index) dupExnDecls =
      [("E", 0), ("E", 1)] := rfl

/-! Oracle line `dup_eids_lookup=SOME 0w`: the repeated name resolves to the
first declaration's ID. -/
theorem dup_exn_eids_lookup :
    lookupInfo "E" (crepGetEidsFromDecls (fun index => index) dupExnDecls) =
      some 0 := by
  decide

/-! Oracle line `mixed_eids_lookup_a=SOME 0w`. -/
theorem mixed_exn_eids_lookup_a :
    lookupInfo "A" (crepGetEidsFromDecls (fun index => index) mixedExnDecls) =
      some 0 := by
  decide

/-! Oracle line `mixed_eids_lookup_e=SOME 1w`: the first `E` declaration is at
index 1, so the repeated name keeps ID 1. -/
theorem mixed_exn_eids_lookup_e :
    lookupInfo "E" (crepGetEidsFromDecls (fun index => index) mixedExnDecls) =
      some 1 := by
  decide

/-- Exception table exactly as the production entrypoint builds it: the
declaration list is scanned only for exception declarations. -/
def dupProbeContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions :=
      crepGetEidsFromDecls (fun index => index) dupExnDecls,
    maxVar := 0, bytesInWord := 1 }

/-- Minimal program raising the duplicated exception. -/
def dupProbeProgram : Prog Nat := .raise "E" (.const 7)

/-- Boolean form of the intermediate exception-ID oracle lines
`dup_eids_lookup`, `mixed_eids_lookup_a`, `mixed_eids_lookup_e`. -/
def dupExnEidsGuard : Bool :=
  (crepGetEidsFromDecls (fun index => index) dupExnDecls == [("E", 0), ("E", 1)]) &&
    (lookupInfo "E" (crepGetEidsFromDecls (fun index => index) dupExnDecls) == some 0) &&
    (lookupInfo "A" (crepGetEidsFromDecls (fun index => index) mixedExnDecls) == some 0) &&
    (lookupInfo "E" (crepGetEidsFromDecls (fun index => index) mixedExnDecls) == some 1)

/-- Boolean form of the compiled-Crep oracle line
`dup_compile=[(«f»,[],Seq (Dec 1 (Const 7w) (Seq (StoreGlob 0w (Var 1)) Skip))
(Raise 0w))]`: the raise carries the first declaration's ID and the payload goes
through the global temporaries. -/
def dupCompileGuard : Bool :=
  match compileProg dupProbeContext dupProbeProgram with
  | .seq (.dec 1 (.const 7) (.seq (.storeGlob 0 (.var 1)) .skip)) (.raise 0) => true
  | _ => false

theorem dup_exn_eids_guard : dupExnEidsGuard = true := by
  decide

#eval dupExnEidsGuard
#guard dupExnEidsGuard
#eval dupCompileGuard
#guard dupCompileGuard

def runChecks : IO Bool := do
  if dupExnEidsGuard then
    IO.println "PASS duplicate exception eids first-binding parity"
  else
    IO.println "FAIL duplicate exception eids parity"
  if dupCompileGuard then
    IO.println "PASS duplicate exception compiled raise parity"
  else
    IO.println "FAIL duplicate exception compiled raise parity"
  pure (dupExnEidsGuard && dupCompileGuard)

end Flapjack.Test.DupExnEidsParity
