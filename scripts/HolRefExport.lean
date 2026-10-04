import Flapjack.Compiler.Backend.StackProps.EvaluateMono
import Flapjack.Compiler.Backend.StackProps.EvaluateNeutral
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Nonrecursive
import Flapjack.Misc.BytesInMemory.Domain
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.FFI
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.ShMemOp
import Flapjack.Compiler.Backend.StackRemove.Proofs.WriteBytearrayFrame
import Flapjack.Compiler.Backend.StackRemove.Proofs.WriteBytearray
import Flapjack.Misc.Sptree.Subspt
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMoveDistinct
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSACutEnvsDomain
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticStoreConsts
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsDelete
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticBufferWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticMove
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsForceRename
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticIf
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticHeap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRaise
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticReturn
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstConst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstBinop
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstShift
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstDiv
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLongMul
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLongDiv
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstAddCarry
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstAddOverflow
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstSubOverflow
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLoad
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLoad8
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstLoad32
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstStore
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstStore8
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstStore32
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstFPCompare
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstFPUnary
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstFPArith
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstFPInt
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstFPMovToReg
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstFPMovFromReg
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstCommon
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticMustTerminate
import Flapjack.Compiler.Backend.StackRemove.ProgComp
import Flapjack.Compiler.Backend.StackRemove.Comp
import Flapjack.Compiler.Backend.StackRemove.CopyLoop
import Flapjack.Compiler.Backend.StackLang.InstBuilders
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticStateWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVars
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileListProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileLookupProps
import Flapjack.Compiler.Backend.StackRemove.StoreAddress
import Flapjack.Compiler.Backend.StackRemove.StackAlloc
import Flapjack.Compiler.Backend.StackRemove.StackAddress
import Flapjack.Compiler.Backend.StackRemove.StackFree
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileGetVars
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcileEmpty
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcile
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopTable
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticPrimitives
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramProps
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsPrimitives
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Encoding
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Padding
import Flapjack.Compiler.Encoders.AsmProps.ArithmeticPreservation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramPropsCalls
import Flapjack.Compiler.Backend.StackProps.InstructionConstants
import Flapjack.Compiler.Backend.StackProps.ClockSupport
import Flapjack.Compiler.Backend.StackProps.ExpressionClock
import Flapjack.Compiler.Backend.StackProps.StateConstants
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmConventions
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameFlat
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameInstructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameShare
import Flapjack.Pancake.WordConvs.FullInstOkLess
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameHelpers
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmRemoveCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmRemoveHelpers
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackConventions
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundRecursive
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundFlat
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundInstructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallArgsCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnCallArgs
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundMono
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnRegisterBounds
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Compiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.RecursiveCalls
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Flat
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Instructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnAllocArgs
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnLabels
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
import Flapjack.Compiler.Backend.WordToStack.Proofs.MoveReconstruction
import Flapjack.Compiler.Backend.WordToStack.Proofs.ALookupMap
import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeInsertWf
import Flapjack.Compiler.Backend.WordToStack.Proofs.ConstMemoryAppend
import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeAccessors
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallLocalRecovery
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackSuffix
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexReconstruction
import Flapjack.Compiler.Backend.WordToStack.Proofs.SourceFrameSize
import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedAList
import Flapjack.Compiler.Backend.WordToStack.Proofs.FrameOffsets
import Flapjack.Compiler.Backend.WordToStack.Proofs.DecodedFrameShape
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLength
import Flapjack.Compiler.Backend.WordToStack.Proofs.MapBitmap
import Flapjack.Compiler.Backend.WordToStack.Proofs.FilterBitmap
import Flapjack.Compiler.Backend.WordToStack.Proofs.ListUpdate
import Flapjack.Compiler.Backend.WordToStack.Proofs.ListUpdateSlices
import Flapjack.Compiler.Backend.WordToStack.Proofs.TopLabelSafety
import Flapjack.Compiler.Backend.WordToStack.Proofs.WordExtraction
import Flapjack.Compiler.Backend.WordToStack.Proofs.WordListLength
import Flapjack.Compiler.Backend.WordToStack.Proofs.LiveListSupport
import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedRelations
import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedKeys
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWrite
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapFrameUpdates
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapInsert
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapDecode
import Flapjack.Compiler.Backend.WordToStack.Proofs.KeyValueOrder
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapSentinelLength
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapBitStructure
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWordLemmas
import Flapjack.Compiler.Backend.StackProps.RegisterBounds
import Flapjack.Compiler.Backend.WordCse.Proofs.ListOrder
import Flapjack.Compiler.Backend.WordCse.Proofs.DeletionFrames
import Flapjack.Compiler.Backend.WordCse.Proofs.EvaluationFrames
import Flapjack.Compiler.Backend.WordCse.Proofs.LoadEvaluation
import Flapjack.Compiler.Backend.WordCse.Proofs.ArithmeticKeys
import Flapjack.Compiler.Backend.WordCse.Proofs.InsertEquality
import Flapjack.Compiler.Backend.WordCse.Proofs.KeyInjectivity
import Flapjack.Compiler.Backend.WordCse.InstructionKeys
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallTop
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallCode
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallPrograms
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopTop
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrograms
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemop
import Flapjack.Compiler.Backend.LabProps.Native
import Flapjack.Compiler.Backend.StackToLab.Native
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrimitives
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopCalls
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemop.Handlers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LimitVar.Properties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMovePreserve
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAOptionLookupSubset
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenamePropertyWrappers
import Flapjack.Pancake.LoopToWord.Proofs.ProgramNames
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveLookups
import Flapjack.Pancake.LoopToWord.Proofs.LabelHandlers
import Flapjack.Pancake.WordConvs.PredicateEquations
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalStateUpdates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.CorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapStep
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert
import Flapjack.Compiler.Backend.WordToStack.Proofs.CodeLabelSafety
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsSwap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalInsert
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveDomains
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.EvenListDistinct
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveFrame
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.MoveHead
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.CorrectRight
import Flapjack.Compiler.Backend.WordAlloc.LimitVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameProperties
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterFlip
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapExtend
import Flapjack
import Flapjack.Compiler.Backend.WordAlloc.Instructions
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConstsGuard
import Flapjack.Compiler.Backend.Semantics.StackSem.FpRegisterInstructions
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval.Load
import Flapjack.Pancake.PanCommon
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpVmax
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.Primop
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.WordLang





open Lean Elab Command Flapjack

/-! List every `@[hol]`-tagged declaration with the qualifiers recorded by its
elaborated attribute and, for declarations without `(reals_as_rational_cuts)`,
whether its constant closure reaches one that carries it. Consumed by
`check_hol_ref_export.py`, which compares both against the theorem map. -/

/-- The body of a tagged definition or `opaque` declaration, if present. -/
private def definitionBody? : ConstantInfo → Option Expr
  | .defnInfo value => some value.value
  | .opaqueInfo value => some value.value
  | _ => none

/-- Constants mentioned by a declaration for the inherited-assumption closure:
    its type, and its body when it is a definition. Theorem proofs are not
    followed. -/
private def closureEdges (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  match definitionBody? info with
  | some body => fromType ++ body.getUsedConstants
  | none => fromType

/-- Whether a declaration's type (and body, for a definition) transitively
    reaches a `(reals_as_rational_cuts)`-tagged declaration through Flapjack
    definitions and datatypes. `known` caches both outcomes soundly: a `true`
    result is cached when found, and when a traversal is exhausted without a
    hit every visited constant is cached as `false` (its closure lies inside
    the visited set). -/
private def reachesRealsCuts (env : Environment) (realsTagged : NameSet)
    (known : Std.HashMap Name Bool) (root : Name) : Bool × Std.HashMap Name Bool := Id.run do
  let flapjackModule (constName : Name) : Bool :=
    match env.getModuleIdxFor? constName with
    | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `Flapjack
    | none => true
  let mut known := known
  let mut visited : NameSet := {}
  let mut stack : Array Name :=
    match env.find? root with
    | some info => closureEdges info
    | none => #[]
  while !stack.isEmpty do
    let current := stack.back!
    stack := stack.pop
    if visited.contains current then continue
    visited := visited.insert current
    if realsTagged.contains current then
      return (true, known.insert root true)
    match known.get? current with
    | some true => return (true, known.insert root true)
    | some false => continue
    | none => pure ()
    if !flapjackModule current then continue
    match env.find? current with
    | some info =>
        match info with
        | .thmInfo _ => pure ()
        | _ => stack := stack ++ closureEdges info
    | none => pure ()
  for constName in visited.toList do
    known := known.insert constName false
  return (false, known.insert root false)

elab "#emit_hol_ref_export" : command => do
  let env ← getEnv
  let realsTagged : NameSet := (HolRef.all env).foldl
    (fun acc (entry : Name × HolRef) => if entry.2.realsAsRationalCuts then acc.insert entry.1 else acc) {}
  let mut known : Std.HashMap Name Bool := {}
  for (name, ref) in HolRef.all env do
    match env.find? name with
    | none => throwError "missing declaration {name}"
    | some _ =>
        let mut qualifiers : List (String × Json) := [
          ("list_as_array", toJson ref.listAsArray),
          ("names_as_string", toJson ref.namesAsString),
          ("names_as_string_boundary", toJson ref.namesAsStringBoundary),
          ("fmap_as_finite_support", toJson ref.fmapAsFiniteSupport),
          ("fmap_as_finite_support_result", toJson ref.fmapAsFiniteSupportResult),
          ("fmap_as_finite_support_function", toJson ref.fmapAsFiniteSupportFunction),
          ("fmap_as_finite_support_result_observations", toJson ref.fmapAsFiniteSupportResultObservations),
          ("fmap_as_finite_support_parameters", toJson ref.fmapAsFiniteSupportParameters),
          ("fmap_as_finite_support_existentials", toJson ref.fmapAsFiniteSupportExistentials),
          ("fmap_as_finite_support_relation",
            toJson (ref.fmapAsFiniteSupportRelation.map (fun entry => if entry.1.isEmpty then entry.2 else s!"{entry.1}.{entry.2}"))),
          ("fmap_as_finite_support_equalities", toJson ref.fmapAsFiniteSupportEqualities),
          ("words_as_type_indexed_bitvec", toJson ref.wordsAsTypeIndexedBitvec)]
        if ref.fmapAsFiniteSupportEquality then
          qualifiers := qualifiers ++ [("fmap_as_finite_support_equality", toJson true)]
        if !ref.fmapAsFiniteSupportHeterogeneousFunction.isEmpty then
          qualifiers := qualifiers ++ [
            ("fmap_as_finite_support_heterogeneous_function",
              toJson ref.fmapAsFiniteSupportHeterogeneousFunction)]
        if let some width := ref.wordDimensionAsWidth then
          qualifiers := qualifiers ++ [("word_dimension_as_width", toJson width)]
        if !ref.wordDimensionsAsWidths.isEmpty then
          qualifiers := qualifiers ++ [("word_dimensions_as_widths", toJson ref.wordDimensionsAsWidths)]
        if ref.realsAsRationalCuts then
          qualifiers := qualifiers ++ [("reals_as_rational_cuts", toJson true)]
        let mut fields : List (String × Json) := [
          ("lean_name", toJson name.toString),
          ("hol_path", toJson ref.path),
          ("hol_name", toJson ref.name),
          ("qualifiers", Json.mkObj qualifiers)]
        if !ref.realsAsRationalCuts then
          let (reaches, known') := reachesRealsCuts env realsTagged known name
          known := known'
          if reaches then
            fields := fields ++ [("inherits_reals_as_rational_cuts", toJson true)]
        liftIO <| IO.println (Json.mkObj fields).compress

#emit_hol_ref_export
