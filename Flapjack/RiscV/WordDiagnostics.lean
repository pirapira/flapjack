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

/-- Collect the foreign-function names referenced by `ffi` nodes in a Word
    program.  The source-facing entrypoint uses this to register the services
    that an original Pancake program may call. -/
def wordProgFfiNames : WordProg α → List FunName
  | .seq first second => wordProgFfiNames first ++ wordProgFfiNames second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgFfiNames thenBranch ++ wordProgFfiNames elseBranch
  | .loop _ body _ | .mustTerminate body => wordProgFfiNames body
  | .call returns _ _ handler =>
      (match returns with
       | some (_, _, returnCode, _, _) => wordProgFfiNames returnCode
       | none => []) ++
        (match handler with
         | some (_, body, _, _) => wordProgFfiNames body
         | none => [])
  | .ffi function _ _ _ _ _ => [function]
  | _ => []
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

def wordToStackProgWordChecked [NeZero width]
    (config : WordStackConfig) (program : WordProg (Word width)) :
    Except WordLoweringError (StackProg Nat) :=
  wordToStackProgNatChecked config (wordProgToNat program)

end Flapjack.RiscV
