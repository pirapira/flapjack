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

/- The bitmap-aware Cake frame path is required not only for foreign calls but
   also for Word constructors that allocate or install constant data.  The
   old selector looked only at FFI names, so an ordinary allocating function
   was sent through the stateless lowering and failed with an empty path. -/
def wordProgHasFrameOperations : WordProg α → Bool
  | .seq first second =>
      wordProgHasFrameOperations first || wordProgHasFrameOperations second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgHasFrameOperations thenBranch || wordProgHasFrameOperations elseBranch
  | .loop _ body _ | .mustTerminate body => wordProgHasFrameOperations body
  | .call returns _ _ handler =>
      (match returns with
       | some (_, _, returnCode, _, _) => wordProgHasFrameOperations returnCode
       | none => false) ||
        (match handler with
         | some (_, body, _, _) => wordProgHasFrameOperations body
         | none => false)
  | .alloc _ _ | .storeConsts _ _ _ _ _ => true
  | _ => false
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

def wordProgNeedsCakeFrame (program : WordProg α) : Bool :=
  !(wordProgFfiNames program).isEmpty || wordProgHasFrameOperations program

def wordToStackProgNatChecked [BEq Nat]
    (config : WordStackConfig) (program : WordProg Nat) :
    Except WordLoweringError (StackProg Nat) :=
  match wordToStackProgNat config program with
  | some stackProgram => .ok stackProgram
  | none =>
      match wordProgFirstUnsupported program with
      | some (path, feature) => .error { path, feature }
      | none => .error { path := [], feature := .loweringFailure }

/-! A state-independent locator for the common expression failure in the
    bitmap-aware lowering path.  That API predates checked errors and returns
    only `none`; this walk retains the sequence path for a failed nested
    expression without changing executable lowering.  Stateful failures that
    are not expression-related intentionally fall back to an empty path. -/
def wordProgFirstExpressionLoweringFailure (config : WordStackConfig) :
    WordProg Nat → Option (List Nat)
  | .seq first second =>
      match wordProgFirstExpressionLoweringFailure config first with
      | some path => some (0 :: path)
      | none =>
          (wordProgFirstExpressionLoweringFailure config second).map
            (fun path => 1 :: path)
  | .ite _operator condition right thenBranch elseBranch =>
      match wordStackConditionOperands config condition right with
      | none => some []
      | some _ =>
          match wordProgFirstExpressionLoweringFailure config thenBranch with
          | some path => some (0 :: path)
          | none =>
              (wordProgFirstExpressionLoweringFailure config elseBranch).map
                (fun path => 1 :: path)
  | .loop _ body _ | .mustTerminate body =>
      (wordProgFirstExpressionLoweringFailure config body).map
        (fun path => 0 :: path)
  | .assign destination value =>
      match wordStackCompileExpToPhysicalNat config destination value with
      | some _ => none
      | none => some []
  | .store address value =>
      let result := match address with
        | .const _ | .var _ | .lookup _ =>
            wordStackCompileStoreNat config address (.var value)
        | _ => wordStackCompileStoreNatNested config address (.var value)
      match result with
      | some _ => none
      | none => some []
  | .set store value =>
      match wordStackSetNat config store value with
      | some _ => none
      | none => some []
  | .shareInst operator name address =>
      match address with
      | .var address =>
          match (wordStackSharedMemoryInst config operator name address :
              Option (StackProg Nat)) with
          | some _ => none
          | none => some []
      | _ => some []
  | .call returns _ _ handler =>
      match returns with
      | some (_, _, returnCode, _, _) =>
          match wordProgFirstExpressionLoweringFailure config returnCode with
          | some path => some (0 :: path)
          | none =>
              match handler with
              | some (_, body, _, _) =>
                  (wordProgFirstExpressionLoweringFailure config body).map
                    (fun path => 1 :: path)
              | none => none
      | none =>
          match handler with
          | some (_, body, _, _) =>
              (wordProgFirstExpressionLoweringFailure config body).map
                (fun path => 1 :: path)
          | none => none
  | _ => none
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def wordToStackProgWordChecked [NeZero width]
    (config : WordStackConfig) (program : WordProg (Word width)) :
    Except WordLoweringError (StackProg Nat) :=
  wordToStackProgNatChecked config (wordProgToNat program)

end Flapjack.RiscV
