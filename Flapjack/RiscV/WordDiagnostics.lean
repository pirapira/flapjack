import Flapjack.RiscV.WordToStack

/-!
# Checked Word-to-Stack diagnostics

The stateless Word-to-Stack API intentionally returns `none` for allocator-
owned `Alloc` and `StoreConsts` nodes because those nodes require the
state-threaded bitmap entrypoint.  This module preserves that API and adds a
checked boundary which identifies the unsupported constructor and its path in
the Word program.
-/

namespace Flapjack.RiscV

inductive WordUnsupportedFeature where
  | alloc
  | storeConsts
  | loweringFailure
  deriving DecidableEq, Repr

structure WordLoweringError where
  path : List Nat
  feature : WordUnsupportedFeature
  deriving DecidableEq, Repr

def wordProgFirstUnsupported : WordProg α → Option (List Nat × WordUnsupportedFeature)
  | .alloc _ _ => some ([], .alloc)
  | .storeConsts _ _ _ _ _ => some ([], .storeConsts)
  | .seq first second =>
      match wordProgFirstUnsupported first with
      | some (path, feature) => some (0 :: path, feature)
      | none =>
          match wordProgFirstUnsupported second with
          | some (path, feature) => some (1 :: path, feature)
          | none => none
  | .ite _ _ _ thenBranch elseBranch =>
      match wordProgFirstUnsupported thenBranch with
      | some (path, feature) => some (0 :: path, feature)
      | none =>
          match wordProgFirstUnsupported elseBranch with
          | some (path, feature) => some (1 :: path, feature)
          | none => none
  | .loop _ body _ | .mustTerminate body =>
      (wordProgFirstUnsupported body).map (fun (path, feature) => (0 :: path, feature))
  | .call returns _ _ handler =>
      match returns with
      | some (_, _, returnCode, _, _) =>
          match wordProgFirstUnsupported returnCode with
          | some (path, feature) => some (0 :: path, feature)
          | none =>
              match handler with
              | none => none
              | some (_, body, _, _) =>
                  (wordProgFirstUnsupported body).map
                    (fun (path, feature) => (0 :: path, feature))
      | none =>
          match handler with
          | none => none
          | some (_, body, _, _) =>
              (wordProgFirstUnsupported body).map
                (fun (path, feature) => (0 :: path, feature))
  | _ => none
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def wordToStackProgNatChecked [BEq Nat]
    (config : WordStackConfig) (program : WordProg Nat) :
    Except WordLoweringError (StackProg Nat) :=
  match wordToStackProgNat config program with
  | some stackProgram => .ok stackProgram
  | none =>
      match wordProgFirstUnsupported program with
      | some (path, feature) => .error { path, feature }
      | none => .error { path := [], feature := .loweringFailure }

end Flapjack.RiscV
