import Flapjack.Pipeline
import Flapjack.Semantics
import Flapjack.LoopSemantics
import Flapjack.RiscV.Backend
import Flapjack.WordSemantics

/-!
Initial end-to-end correctness theorem for the executable Flapjack pipeline.

This module deliberately starts with a small, fully parameterized RV64
function. It connects the source Pancake evaluator to the artifact emitted by
the complete front-end/Loop/Word/RISC-V composition; larger simulation
relations can be added beside this theorem as more instructions and states are
ported.
-/

namespace Flapjack

def pipelineAddDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "add", inline := false, exported := false,
      params := [("left", .one), ("right", .one)],
      body := .return (.op .add
        [.var .local "left", .var .local "right"]), returnShape := .one }]

def pipelineAddPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineAddDeclarations

def pipelineAddFunctions := pipelineAddPipeline.functions

def pipelineAddLinkedFunctions := pipelineAddPipeline.linkedFunctions

theorem pipelineAddFunctions_shape :
    pipelineAddFunctions =
      [(1, [2, 3], some ([.add 5 2 3], [5]))] := by
  native_decide

theorem pipelineAddLinkedFunctions_shape :
    pipelineAddLinkedFunctions =
      some [(1, 0, [2, 3], [.add 5 2 3], [5])] := by
  change RiscV.linkRiscVFunctions 0 pipelineAddFunctions = _
  rw [pipelineAddFunctions_shape]
  rfl

def compiledPipelineAddRun (left right : RiscV.Word 64) :
    Option (List (RiscV.Word 64)) :=
  match pipelineAddLinkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 10 entry parameters code returns
            [left, right] (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineAddSource (left right : RiscV.Word 64) : Prog (RiscV.Word 64) :=
  .return (.op .add [.var .local "left", .var .local "right"])

def pipelineAddLocals (left right : RiscV.Word 64) :
    VarName → Option (RiscV.Word 64) :=
  fun name => if name == "left" then some left
    else if name == "right" then some right else none

theorem compiledPipelineAdd_correct (left right : RiscV.Word 64) :
    compiledPipelineAddRun left right =
      evalPanProg (pipelineAddLocals left right) (pipelineAddSource left right) := by
  simp [compiledPipelineAddRun, pipelineAddLinkedFunctions_shape,
    pipelineAddSource, pipelineAddLocals, evalPanProg, evalPanExp]
  exact RiscV.executeFunction_add_general left right

def pipelineMulDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "mul", inline := false, exported := false, params := [],
      body := .return (.panOp .mul
        [.const (BitVec.ofNat 64 2), .const (BitVec.ofNat 64 3)]),
      returnShape := .one }]

def pipelineMulPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineMulDeclarations

def pipelineMulLinkedFunctions := pipelineMulPipeline.linkedFunctions

theorem pipelineMulFunctions_shape :
    pipelineMulPipeline.functions =
      [(1, [], some ([.addi 3 0 (BitVec.ofNat 64 2),
        .addi 4 0 (BitVec.ofNat 64 3), .mulHU 5 3 4, .mul 5 3 4,
        .addi 6 5 0], [6]))] := by
  native_decide

theorem pipelineMulLinkedFunctions_shape :
    pipelineMulLinkedFunctions =
      some [(1, 0, [],
        [.addi 3 0 (BitVec.ofNat 64 2), .addi 4 0 (BitVec.ofNat 64 3),
          .mulHU 5 3 4, .mul 5 3 4, .addi 6 5 0], [6])] := by
  change RiscV.linkRiscVFunctions 0 pipelineMulPipeline.functions = _
  rw [pipelineMulFunctions_shape]
  rfl

def compiledPipelineMulRun : Option (List (RiscV.Word 64)) :=
  match pipelineMulLinkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 10 entry parameters code returns []
            (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineMulSource : Prog (RiscV.Word 64) :=
  .return (.panOp .mul
    [.const (BitVec.ofNat 64 2), .const (BitVec.ofNat 64 3)])

theorem compiledPipelineMul_correct :
    compiledPipelineMulRun =
      evalPanProg (fun _ => none) pipelineMulSource := by
  native_decide

def pipelineIteDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "ite", inline := false, exported := false, params := [],
      body := .ite (.const (BitVec.ofNat 64 1))
        (.return (.const (BitVec.ofNat 64 7)))
        (.return (.const (BitVec.ofNat 64 8))), returnShape := .one }]

def pipelineItePipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineIteDeclarations

def compiledPipelineIteRun : Option (List (RiscV.Word 64)) :=
  match pipelineItePipeline.linkedFunctions with
  | some [(_, entry, parameters, code, returns)] =>
      match parameters.mapM RiscV.registerOfNat with
      | some parameters =>
          RiscV.executeFunction 40 entry parameters code returns []
            (RiscV.zeroState 64)
      | none => none
  | _ => none

def pipelineIteSource : Prog (RiscV.Word 64) :=
  .ite (.const (BitVec.ofNat 64 1))
    (.return (.const (BitVec.ofNat 64 7)))
    (.return (.const (BitVec.ofNat 64 8)))

theorem compiledPipelineIte_correct :
    compiledPipelineIteRun =
      evalPanProg (fun _ => none) pipelineIteSource := by
  native_decide

/-!
The first end-to-end call regression. The source program uses a declaration
call rather than an unbound low-level call, so the static front end allocates
the result local and the call-aware linker can recover the callee's return
layout. The concrete image also checks the ordinary-call link register
save/restore sequence.
-/
def pipelineCallDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "id", inline := false, exported := false,
      params := [("x", .one)],
      body := .return (.var .local "x"), returnShape := .one },
   .function
    { name := "main", inline := false, exported := true,
      params := [],
      body := .decCall "result" .one "id"
        [.const (BitVec.ofNat 64 41)]
        (.return (.var .local "result")), returnShape := .one }]

def pipelineCallPipeline : FlapjackRiscVResult 64 :=
  compileFlapjackRiscV (width := 64) .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
    pipelineCallDeclarations

theorem pipelineCallLinkedFunctions_available :
    pipelineCallPipeline.callLinkedFunctions.isSome := by
  native_decide

def pipelineCallImage : List (RiscV.Instruction 64) :=
  [.addi 4 2 0, .jalr 0 1 0,
   .addi 3 0 0, .addi 4 0 (BitVec.ofNat 64 41),
   .addi 2 4 0, .addi 30 30 (0 - BitVec.ofNat 64 8),
   .storeWord 1 30, .addi 31 0 0, .jalr 1 31 0,
   .addi 3 4 0, .loadWord 1 30,
   .addi 30 30 (BitVec.ofNat 64 8), .addi 4 3 0,
   .jalr 0 1 0]

def pipelineCallLinkedImage : Option (List (RiscV.Instruction 64)) :=
  pipelineCallPipeline.callLinkedFunctions.map (fun entries =>
    entries.flatMap (fun item =>
      let (_, _, _, code, _) := item
      code))

theorem pipelineCallLinkedImage_shape :
    pipelineCallLinkedImage = some pipelineCallImage := by
  native_decide

theorem pipelineCall_word_semantics :
    (do
      let (_, main) ←
        RiscV.lookupWordFunction 2 pipelineCallPipeline.pipeline.word
      let (_, values) ←
        RiscV.evalWordFunctionWithCalls pipelineCallPipeline.pipeline.word
          30 (RiscV.zeroState 64) main
      pure values) = some [BitVec.ofNat 64 41] := by
  native_decide

theorem pipelineCall_compiled_execution :
    RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 8 100 []
      pipelineCallImage [4] []
      (RiscV.writeRegister (RiscV.zeroState 64) 1 100) =
      some [BitVec.ofNat 64 41] := by
  native_decide

theorem pipelineCall_generated_compiled_execution :
    (do
      let image ← pipelineCallLinkedImage
      RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 8 100 []
        image [4] []
        (RiscV.writeRegister (RiscV.zeroState 64) 1 100)) =
      some [BitVec.ofNat 64 41] := by
  rw [pipelineCallLinkedImage_shape]
  exact pipelineCall_compiled_execution

def pipelineCallSourceFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("id", ["x"], .return (.var .local "x"))]

def pipelineCallSourceMain : Prog (RiscV.Word 64) :=
  .decCall "result" .one "id"
    [.const (BitVec.ofNat 64 41)]
    (.return (.var .local "result"))

theorem pipelineCall_source_semantics :
    (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
      pipelineCallSourceMain).map (fun result => result.2) =
      some [BitVec.ofNat 64 41] := by
  native_decide

def pipelineHandlerSourceFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("raise", [], .raise "E" (.const (BitVec.ofNat 64 7)))]

def pipelineHandlerSourceMain : Prog (RiscV.Word 64) :=
  .call
    (some (none, some ("E", "exception",
      .return (.var .local "exception"))))
    "raise" []

theorem pipelineHandler_source_semantics :
    (evalPanProgWithHandlers pipelineHandlerSourceFunctions 20 (fun _ => none)
      pipelineHandlerSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 7] := by
  native_decide

def pipelineFfiHandler :
    FunName → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 →
      (VarName → Option (RiscV.Word 64)) →
      Option (VarName → Option (RiscV.Word 64)) :=
  fun function configuration _ array _ locals =>
    if function == "inc" then
      some (updatePanLocal locals "result" (configuration + array + 1))
    else none

def pipelineFfiSource : Prog (RiscV.Word 64) :=
  .extCall "inc"
    (.const (BitVec.ofNat 64 41)) (.const (BitVec.ofNat 64 0))
    (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 0))

theorem pipelineFfi_source_semantics :
    (evalPanFfiProg pipelineFfiHandler (fun _ => none) pipelineFfiSource).map
      (fun locals => locals "result") = some (some (BitVec.ofNat 64 42)) := by
  native_decide

def pipelineFfiCallFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("ffiId", ["x"],
      .seq
        (.extCall "inc" (.var .local "x") (.const 0)
          (.const 0) (.const 0))
        (.return (.var .local "result")))]

def pipelineFfiCallMain : Prog (RiscV.Word 64) :=
  .decCall "answer" .one "ffiId"
    [.const (BitVec.ofNat 64 41)]
    (.return (.var .local "answer"))

theorem pipelineFfi_call_source_semantics :
    (evalPanProgWithCallsAndFfi pipelineFfiCallFunctions pipelineFfiHandler 50
      (fun _ => none) pipelineFfiCallMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 42] := by
  native_decide

theorem pipelineCall_source_word_machine_agreement :
    (evalPanProgWithCalls pipelineCallSourceFunctions 20 (fun _ => none)
      pipelineCallSourceMain).map (fun result => result.2) =
        some [BitVec.ofNat 64 41] ∧
      (do
        let (_, main) ←
          RiscV.lookupWordFunction 2 pipelineCallPipeline.pipeline.word
        let (_, values) ←
          RiscV.evalWordFunctionWithCalls pipelineCallPipeline.pipeline.word
            30 (RiscV.zeroState 64) main
        pure values) = some [BitVec.ofNat 64 41] ∧
      (do
        let image ← pipelineCallLinkedImage
        RiscV.executeFunctionAt 120 (0 : RiscV.Word 64) 8 100 []
          image [4] []
          (RiscV.writeRegister (RiscV.zeroState 64) 1 100)) =
        some [BitVec.ofNat 64 41] := by
  exact ⟨pipelineCall_source_semantics, pipelineCall_word_semantics,
    pipelineCall_generated_compiled_execution⟩

/-!
This is the first pass-composed semantic bridge.  It relates a Pancake
constant return to the result of the actual `compileProg` and
`loopCompileProg` passes, using the executable Loop evaluator.  The fixed fuel
bound is sufficient for the generated temporary-assignment sequence and is
deliberately explicit until a general fuel monotonicity theorem is available.
-/
theorem compilePanToLoop_return_const_correct
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (compileContext : CompileContext α) (loopContext : LoopContext α)
    (live : List Nat) (state : LoopState α) (value : α) :
    (evalLoopProg 12 state
      (loopCompileProg loopContext live
        (compileProg compileContext (.return (.const value))))).map loopResultValues =
      evalPanProg (fun _ => none) (.return (.const value)) := by
  simp [compileProg, compileExp, loopCompileProg, loopCompileExp,
    loopCompileExp.loopCompileExps, loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, evalLoopProg, evalLoopExp,
    loopReadLocals, updateLoopLocal, loopResultValues, evalPanProg,
    evalPanExp]

/-!
The first compositional bridge between the Loop and Word semantic states.
Only the destination register is observed here; the full state relation will
add globals, memory, live-register preservation, and control results as the
remaining Word operations are ported.
-/
def loopRegisterState [NeZero width] (state : RiscV.State width) :
    LoopState (RiscV.Word width) :=
  { locals := fun name =>
      (RiscV.registerOfNat name).map (RiscV.readRegister state)
    globals := fun _ => none
    memory := fun _ => none }

def loopRegisterStateMapped [NeZero width] (context : WordContext)
    (state : RiscV.State width) : LoopState (RiscV.Word width) :=
  { locals := fun name =>
      (RiscV.registerOfNat (wordFindVar context name)).map
        (RiscV.readRegister state)
    globals := fun _ => none
    memory := fun _ => none }

def loopRegisterStateMappedWithMemory [NeZero width] (context : WordContext)
    (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width)) :
    LoopState (RiscV.Word width) :=
  { loopRegisterStateMapped context state with memory := memory }

/-!
This is the first context-parametric Loop-to-Word state observation. The
source local and its mapped register need not have the same numeric name; the
only required premise is that the mapped destination is a valid RISC-V
register. It is the base case needed before extending the relation to
expression evaluation and sequencing.
-/
theorem loopToWord_const_assign_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (destination : Nat) (value : RiscV.Word width) (register : Fin 32)
    (zero : RiscV.ZeroRegister state)
    (hregister :
      RiscV.registerOfNat (wordFindVar context destination) = some register)
    (hregister_nonzero : register ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.assign destination (.const value))).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.const value)))).map
        (fun state => RiscV.readRegister state register) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, loopRegisterStateMapped,
    loopToWordProg, wordCompileExp, RiscV.evalWordProg,
    RiscV.wordExpToInstructions, RiscV.wordExpToInstruction,
    RiscV.executeInstructions, RiscV.execute,
    RiscV.writeRegister, RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, hregister, hregister_nonzero, hzero]

theorem loopToWord_add_assign_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (destination left right : Nat) (destinationRegister leftRegister rightRegister : Fin 32)
    (zero : RiscV.ZeroRegister state)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hleft :
      RiscV.registerOfNat (wordFindVar context left) = some leftRegister)
    (hright :
      RiscV.registerOfNat (wordFindVar context right) = some rightRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.assign destination (.op .add [.var left, .var right]))).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.op .add [.var left, .var right])))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, evalLoopBinOp,
    loopRegisterStateMapped, loopToWordProg, wordCompileExp,
    wordCompileExp.wordCompileExpList,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
    RiscV.nextPc, updateLoopLocal, hdestination, hleft, hright,
    hdestination_nonzero, hzero]

theorem loopToWord_binop_assign_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (operator : BinOp) (destination left right : Nat)
    (destinationRegister leftRegister rightRegister : Fin 32)
    (zero : RiscV.ZeroRegister state)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) = some destinationRegister)
    (hleft :
      RiscV.registerOfNat (wordFindVar context left) = some leftRegister)
    (hright :
      RiscV.registerOfNat (wordFindVar context right) = some rightRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.assign destination (.op operator [.var left, .var right]))).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.op operator [.var left, .var right])))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  have hand (x y : RiscV.Word width) : AndOp.and x y = x &&& y := by
    change x.and y = x &&& y
    exact BitVec.and_eq x y
  have hor (x y : RiscV.Word width) : OrOp.or x y = x ||| y := by
    change x.or y = x ||| y
    exact BitVec.or_eq x y
  cases operator <;>
    simp [evalLoopProg, evalLoopExp, evalLoopBinOp,
      loopRegisterStateMapped, loopToWordProg, wordCompileExp,
      wordCompileExp.wordCompileExpList,
      RiscV.evalWordProg, RiscV.wordExpToInstructions,
      RiscV.wordExpToInstruction, RiscV.executeInstructions,
      RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      RiscV.nextPc, updateLoopLocal, hdestination, hleft, hright,
      hdestination_nonzero, hzero, hand, hor]

theorem loopToWord_locValue_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (destination source : Nat) (destinationRegister sourceRegister : Fin 32)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) = some destinationRegister)
    (hsource :
      RiscV.registerOfNat (wordFindVar context source) = some sourceRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMapped context state)
      (.locValue destination source)).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context (.locValue destination source))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  simp [evalLoopProg, loopRegisterStateMapped, loopToWordProg,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions, RiscV.execute,
    RiscV.writeRegister, RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, hdestination, hsource, hdestination_nonzero]

theorem loopToWord_load32_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address destination : Nat) (addressRegister destinationRegister : Fin 32)
    (addressValue value : RiscV.Word width)
    (zero : RiscV.ZeroRegister state)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hmemory : memory addressValue = some value)
    (hmachine : RiscV.readWord32 state addressValue = value)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.load32 address destination)).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context (.load32 address destination))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, loopRegisterStateMappedWithMemory,
    loopRegisterStateMapped, loopToWordProg, wordCompileExp,
    RiscV.evalWordProg, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, haddress, hdestination, haddress_value,
    hmemory, hmachine, hdestination_nonzero, hzero]
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  rw [haddress_value', hmemory, hmachine]
  simp [updateLoopLocal]

theorem loopToWord_loadByte_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address destination : Nat) (addressRegister destinationRegister : Fin 32)
    (addressValue value : RiscV.Word width) (byteValue : BitVec 8)
    (zero : RiscV.ZeroRegister state)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hmemory :
      memory addressValue =
        some (BitVec.ofNat width byteValue.toNat))
    (hmachine :
      RiscV.readByte state addressValue = byteValue)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.shMem .load8 destination (.var address))).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .load8 destination (.var address)))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  have haddress_eval :
      evalLoopExp (loopRegisterStateMappedWithMemory context state memory)
        (.var address) = some addressValue := by
    simp [evalLoopExp, loopRegisterStateMappedWithMemory,
      loopRegisterStateMapped, haddress, haddress_value]
  rw [evalLoopProg_shMem_load
    (loopRegisterStateMappedWithMemory context state memory) .load8
    destination (.var address) addressValue
    (BitVec.ofNat width byteValue.toNat) (by simp) haddress_eval hmemory]
  simp [loopRegisterStateMappedWithMemory, loopRegisterStateMapped,
    loopToWordProg, wordMemOp, wordCompileExp, RiscV.evalWordProg,
    RiscV.evalWordShareInst, RiscV.wordShareInstToInstructions,
    RiscV.wordInstToInstruction, RiscV.executeInstructions, RiscV.execute,
    RiscV.writeRegister, RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, haddress, hdestination, haddress_value, hmachine,
    hdestination_nonzero, hzero]
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  rw [haddress_value', hmachine]

theorem loopToWord_storeByte_memory_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address value : Nat) (addressRegister valueRegister : Fin 32)
    (addressValue valueValue : RiscV.Word width)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hvalue_value :
      RiscV.readRegister state valueRegister = valueValue) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.shMem .store8 value (.var address))).bind (fun result =>
        match result with
        | .normal state =>
            (state.memory addressValue).map
              (fun value => BitVec.ofNat width (value.toNat % 256))
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .store8 value (.var address)))).map
        (fun state =>
          BitVec.ofNat width
            (RiscV.readByte state addressValue).toNat) := by
  have haddress_eval :
      evalLoopExp (loopRegisterStateMappedWithMemory context state memory)
        (.var address) = some addressValue := by
    simp [evalLoopExp, loopRegisterStateMappedWithMemory,
      loopRegisterStateMapped, haddress, haddress_value]
  have hvalue_eval :
      (loopRegisterStateMappedWithMemory context state memory).locals value =
        some valueValue := by
    simp [loopRegisterStateMappedWithMemory, loopRegisterStateMapped,
      hvalue, hvalue_value]
  rw [evalLoopProg_shMem_store
    (loopRegisterStateMappedWithMemory context state memory) .store8
    value (.var address) addressValue valueValue
    (by simp) haddress_eval hvalue_eval]
  simp [loopRegisterStateMappedWithMemory, loopRegisterStateMapped,
    loopToWordProg, wordMemOp, wordCompileExp, RiscV.evalWordProg,
    RiscV.evalWordShareInst, RiscV.wordShareInstToInstructions,
    RiscV.wordInstToInstruction, RiscV.executeInstructions, RiscV.execute,
    RiscV.writeByte, RiscV.readByte, RiscV.byteAddress, RiscV.nextPc,
    haddress, hvalue, haddress_value, hvalue_value, updateLoopMemory]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod]

theorem loopToWord_load16_register_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address destination : Nat) (addressRegister destinationRegister : Fin 32)
    (addressValue value : RiscV.Word width)
    (zero : RiscV.ZeroRegister state)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hmemory : memory addressValue = some value)
    (hmachine : RiscV.readWord16 state addressValue = value)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.shMem .load16 destination (.var address))).bind (fun result =>
        match result with
        | .normal state => state.locals destination
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .load16 destination (.var address)))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  have haddress_eval :
      evalLoopExp (loopRegisterStateMappedWithMemory context state memory)
        (.var address) = some addressValue := by
    simp [evalLoopExp, loopRegisterStateMappedWithMemory,
      loopRegisterStateMapped, haddress, haddress_value]
  rw [evalLoopProg_shMem_load
    (loopRegisterStateMappedWithMemory context state memory) .load16
    destination (.var address) addressValue value (by simp) haddress_eval hmemory]
  simp [loopRegisterStateMappedWithMemory, loopRegisterStateMapped,
    loopToWordProg, wordMemOp, wordCompileExp, RiscV.evalWordProg,
    RiscV.evalWordShareInst, RiscV.wordShareInstToInstructions,
    RiscV.wordInstToInstruction, RiscV.executeInstructions, RiscV.execute,
    RiscV.writeRegister, RiscV.readRegister, RiscV.nextPc,
    updateLoopLocal, haddress, hdestination, haddress_value, hmachine,
    hdestination_nonzero, hzero]
  have haddress_value' : state.registers addressRegister = addressValue := by
    exact haddress_value
  rw [haddress_value', hmachine]

theorem loopToWord_store16_memory_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address value : Nat) (addressRegister valueRegister : Fin 32)
    (addressValue valueValue : RiscV.Word width)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hvalue_value :
      RiscV.readRegister state valueRegister = valueValue) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.shMem .store16 value (.var address))).bind (fun result =>
        match result with
        | .normal state =>
            (state.memory addressValue).map
              (fun value => BitVec.ofNat width (value.toNat % 256))
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.shMem .store16 value (.var address)))).map
        (fun state =>
          BitVec.ofNat width
            (RiscV.readByte state (RiscV.byteAddress addressValue 0)).toNat) := by
  simp [evalLoopProg, evalLoopExp, loopRegisterStateMappedWithMemory,
    loopRegisterStateMapped, loopToWordProg, wordMemOp, wordCompileExp,
    RiscV.evalWordProg, RiscV.evalWordShareInst,
    RiscV.wordShareInstToInstructions, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.wordInstToInstruction,
    RiscV.executeInstructions, RiscV.execute, RiscV.writeWord16,
    RiscV.writeByte, RiscV.readByte, RiscV.byteAddress, RiscV.nextPc,
    haddress, hvalue, haddress_value, hvalue_value, updateLoopMemory]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod, NeZero.ne width]

theorem loopToWord_store32_memory_agreement_mapped [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (memory : RiscV.Word width → Option (RiscV.Word width))
    (address value : Nat) (addressRegister valueRegister : Fin 32)
    (addressValue valueValue : RiscV.Word width)
    (haddress :
      RiscV.registerOfNat (wordFindVar context address) = some addressRegister)
    (hvalue :
      RiscV.registerOfNat (wordFindVar context value) = some valueRegister)
    (haddress_value :
      RiscV.readRegister state addressRegister = addressValue)
    (hvalue_value :
      RiscV.readRegister state valueRegister = valueValue)
    (width_ge_8 : 8 ≤ width) :
    (evalLoopProg 1 (loopRegisterStateMappedWithMemory context state memory)
      (.store32 address value)).bind (fun result =>
        match result with
        | .normal state =>
            (state.memory addressValue).map
              (fun value => BitVec.ofNat width (value.toNat % 256))
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context (.store32 address value))).map
        (fun state =>
          BitVec.ofNat width
            (RiscV.readByte state (RiscV.byteAddress addressValue 0)).toNat) := by
  have hwidth0 : width ≠ 0 := NeZero.ne width
  have h2 : (BitVec.ofNat width 2) ≠ 0 := by
    intro h
    have h' := congrArg BitVec.toNat h
    have hpow : 2 ^ 2 ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow' : 4 ≤ 2 ^ width := by
      simpa using hpow
    have hlt : (2 : Nat) < 2 ^ width :=
      Nat.lt_of_lt_of_le (by decide : (2 : Nat) < 4) hpow'
    have h'' : (2 : Nat) = 0 := by
      simpa [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlt] using h'
    omega
  have h3 : (BitVec.ofNat width 3) ≠ 0 := by
    intro h
    have h' := congrArg BitVec.toNat h
    have hpow : 2 ^ 2 ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow' : 4 ≤ 2 ^ width := by
      simpa using hpow
    have hlt : (3 : Nat) < 2 ^ width :=
      Nat.lt_of_lt_of_le (by decide : (3 : Nat) < 4) hpow'
    have h'' : (3 : Nat) = 0 := by
      simpa [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlt] using h'
    omega
  simp [evalLoopProg, loopRegisterStateMappedWithMemory,
    loopRegisterStateMapped, loopToWordProg, RiscV.evalWordProg,
    RiscV.execute, RiscV.writeWord32, RiscV.writeByte,
    RiscV.readByte, RiscV.byteAddress, RiscV.nextPc,
    haddress, hvalue, haddress_value, hvalue_value, updateLoopMemory]
  split <;> rename_i h
  · exact (h3 h).elim
  · split <;> rename_i h'
    · exact (h2 h').elim
    · have hvalue_byte : BitVec.toNat valueValue % 256 < 2 ^ 8 := by
        have hmod := Nat.mod_lt (BitVec.toNat valueValue) (by decide : 0 < 256)
        simpa using hmod
      rw [BitVec.setWidth_ofNat_of_le_of_lt (by omega : 8 ≤ width) hvalue_byte]

theorem loopToWord_const_assign_register_agreement [NeZero width]
    (state : RiscV.State width) (zero : RiscV.ZeroRegister state)
    (value : RiscV.Word width) :
    (evalLoopProg 1 (loopRegisterState state)
      (.assign 1 (.const value))).bind (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.assign 1 (.const value)))).map
        (fun state => RiscV.readRegister state 1) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, loopRegisterState, loopToWordProg, loopToWordExp,
    wordCompileExp, wordFindVar, lookupNatInfo,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, updateLoopLocal, hzero]

theorem loopToWord_add_assign_register_agreement [NeZero width]
    (state : RiscV.State width) (zero : RiscV.ZeroRegister state) :
    (evalLoopProg 1 (loopRegisterState state)
      (.assign 1 (.op .add [.var 2, .var 3]))).bind (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.assign 1 (.op .add [.var 2, .var 3])))).map
        (fun state => RiscV.readRegister state 1) := by
  have hzero : state.registers 0 = (0 : RiscV.Word width) := by
    exact zero
  simp [evalLoopProg, evalLoopExp, evalLoopBinOp, loopRegisterState,
    loopToWordProg, wordCompileExp, wordCompileExp.wordCompileExpList,
    wordFindVar, lookupNatInfo,
    RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, updateLoopLocal, hzero]

theorem loopToWord_longMul_register_agreement [NeZero width]
    (state : RiscV.State width) :
    (evalLoopProg 1 (loopRegisterState state)
      (.arith (.longMul 1 1 2 3))).bind (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.arith (.longMul 1 1 2 3)))).map
        (fun state => RiscV.readRegister state 1) := by
  simp [evalLoopProg, loopRegisterState, loopToWordProg, wordArith,
    wordFindVar, lookupNatInfo, RiscV.evalWordProg,
    RiscV.wordArithToInstructions, RiscV.executeInstructions,
    RiscV.registerOfNat, RiscV.execute, RiscV.writeRegister,
    RiscV.readRegister, RiscV.nextPc, updateLoopLocal]

/-!
The local relation used by the HOL loop_to_word proof is represented here as
a direct register witness.  This theorem lifts the constructor-specific
mapped binop observations above to an arbitrary Loop local environment:
every source local has a mapped RISC-V register carrying the same word, and
the destination mapping is required to be writable.
-/
def loopLocalsMappedToRiscV [NeZero width] (context : WordContext)
    (locals : Nat → Option (RiscV.Word width))
    (state : RiscV.State width) : Prop :=
  ∀ name value, locals name = some value →
    ∃ register,
      RiscV.registerOfNat (wordFindVar context name) = some register ∧
        RiscV.readRegister state register = value

theorem pipelineWordContext_register_nonalias
    (slots : List Nat) (name destination : Nat)
    (hname : name ∈ slots) (hdestination : destination ∈ slots)
    (hneq : name ≠ destination)
    (nameRegister destinationRegister : Fin 32)
    (hname_register :
      RiscV.registerOfNat
        (wordFindVar (pipelineWordContext slots) name) = some nameRegister)
    (hdestination_register :
      RiscV.registerOfNat
        (wordFindVar (pipelineWordContext slots) destination) =
        some destinationRegister) :
    nameRegister ≠ destinationRegister := by
  intro heq
  have hnames := RiscV.registerOfNat_injective hname_register
    hdestination_register heq
  rw [wordFindVar_pipelineWordContext_of_mem slots name hname,
    wordFindVar_pipelineWordContext_of_mem slots destination hdestination] at hnames
  exact hneq (Nat.add_right_cancel hnames)

theorem loopToWordExp_var_agreement_of_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (name : Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hvalue : ∃ value, loopState.locals name = some value) :
    evalLoopExp loopState (.var name) =
      (wordCompileExp context (.var name)).bind
        (RiscV.evalWordExp state) := by
  obtain ⟨value, hvalue⟩ := hvalue
  rcases hlocals name value hvalue with
    ⟨register, hregister, hregister_value⟩
  simp [evalLoopExp, wordCompileExp, RiscV.evalWordExp,
    hvalue, hregister, hregister_value]

theorem loopLocalsMappedToRiscV_update [NeZero width]
    (context : WordContext) (locals : Nat → Option (RiscV.Word width))
    (state : RiscV.State width) (destination : Nat)
    (destinationRegister : Fin 32) (value : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context locals state)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    loopLocalsMappedToRiscV context (updateLoopLocal locals destination value)
      (RiscV.writeRegister state destinationRegister value) := by
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    have hvalue : value = current := by
      simpa [updateLoopLocal] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.writeRegister, RiscV.readRegister, hdestination_nonzero]
  · have hcurrent' : locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp only [RiscV.readRegister, RiscV.writeRegister,
      if_neg hdestination_nonzero]
    simp only [if_neg hregister_nonalias]
    change RiscV.readRegister state register = current
    exact hregister_value

theorem loopToWord_tick_preserves_mapped_locals [NeZero width]
    (context : WordContext) (locals : Nat → Option (RiscV.Word width))
    (state : RiscV.State width)
    (hlocals : loopLocalsMappedToRiscV context locals state) :
    ∀ resultState,
      RiscV.evalWordProg state (.tick : WordProg (RiscV.Word width)) =
        some resultState →
      loopLocalsMappedToRiscV context locals resultState := by
  intro resultState hresult
  simp [RiscV.evalWordProg] at hresult
  subst resultState
  intro name value hvalue
  rcases hlocals name value hvalue with
    ⟨register, hregister, hregister_value⟩
  refine ⟨register, hregister, ?_⟩
  by_cases hzero : register = 0
  · subst register
    exact hregister_value
  · simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister, hzero]
    exact hregister_value

def loopResultMappedToRiscV [NeZero width] (context : WordContext) :
    LoopResult (RiscV.Word width) → RiscV.WordLoopResult width → Prop
  | .normal loopState, .normal state =>
      loopLocalsMappedToRiscV context loopState.locals state
  | .broke loopState loopLabel, .broke state wordLabel =>
      loopLabel = wordLabel ∧
        loopLocalsMappedToRiscV context loopState.locals state
  | .continued loopState loopLabel, .continued state wordLabel =>
      loopLabel = wordLabel ∧
        loopLocalsMappedToRiscV context loopState.locals state
  | _, _ => False

theorem loopRepeat_mapped_locals [NeZero width]
    (context : WordContext) (body : LoopProg (RiscV.Word width))
    (wordBody : WordProg (RiscV.Word width))
    (hbody : ∀ fuel loopState state loopResult wordResult,
      loopLocalsMappedToRiscV context loopState.locals state →
      evalLoopProg fuel loopState body = some loopResult →
      RiscV.evalWordLoopProg fuel state wordBody = some wordResult →
      loopResultMappedToRiscV context loopResult wordResult) :
    ∀ fuel loopState state loopResult wordResult,
      loopLocalsMappedToRiscV context loopState.locals state →
      evalLoopRepeat fuel loopState body = some loopResult →
      RiscV.evalWordLoopRepeat fuel state wordBody = some wordResult →
      loopResultMappedToRiscV context loopResult wordResult := by
  intro fuel
  induction fuel with
  | zero =>
      intro loopState state loopResult wordResult hlocals hloop hword
      simp [evalLoopRepeat, RiscV.evalWordLoopRepeat] at hloop
  | succ fuel ih =>
      intro loopState state loopResult wordResult hlocals hloop hword
      cases hbodyLoop : evalLoopProg fuel loopState body with
      | none =>
          simp [evalLoopRepeat, hbodyLoop] at hloop
      | some loopBodyResult =>
          cases hbodyWord : RiscV.evalWordLoopProg fuel state wordBody with
          | none =>
              simp [RiscV.evalWordLoopRepeat, hbodyWord] at hword
          | some wordBodyResult =>
              have hbodyResult := hbody fuel loopState state
                loopBodyResult wordBodyResult hlocals hbodyLoop hbodyWord
              cases loopBodyResult with
              | normal middleLoop =>
                  cases wordBodyResult with
                  | normal middleWord =>
                      have hlocals' :
                          loopLocalsMappedToRiscV context middleLoop.locals middleWord :=
                        hbodyResult
                      apply ih middleLoop middleWord loopResult wordResult hlocals'
                      · simpa [evalLoopRepeat, hbodyLoop] using hloop
                      · simpa [RiscV.evalWordLoopRepeat, hbodyWord] using hword
                  | broke middleWord label | continued middleWord label =>
                      exact False.elim (by simpa [loopResultMappedToRiscV] using hbodyResult)
              | broke middleLoop label =>
                  cases wordBodyResult with
                  | normal middleWord | continued middleWord wordLabel =>
                      exact False.elim (by simpa [loopResultMappedToRiscV] using hbodyResult)
                  | broke middleWord wordLabel =>
                      have hlabel : label = wordLabel := by
                        exact hbodyResult.1
                      have hlocals' :
                          loopLocalsMappedToRiscV context middleLoop.locals middleWord :=
                        hbodyResult.2
                      by_cases hzero : label = 0
                      · have hwordLabel : wordLabel = 0 := by
                          exact hlabel.symm.trans hzero
                        subst label
                        subst wordLabel
                        have hloop' :
                            some (.normal middleLoop) = some loopResult := by
                          simpa [evalLoopRepeat, hbodyLoop] using hloop
                        have hword' :
                            some (.normal middleWord) = some wordResult := by
                          simpa [RiscV.evalWordLoopRepeat, hbodyWord] using hword
                        cases hloop'
                        cases hword'
                        exact hlocals'
                      · have hwordLabel : wordLabel ≠ 0 := by
                          intro hwordZero
                          apply hzero
                          simpa [hwordZero] using hlabel
                        have hloop' :
                            some (.broke middleLoop label) = some loopResult := by
                          simpa [evalLoopRepeat, hbodyLoop, hzero] using hloop
                        have hword' :
                            some (.broke middleWord wordLabel) = some wordResult := by
                          simpa [RiscV.evalWordLoopRepeat, hbodyWord, hwordLabel] using hword
                        cases hloop'
                        cases hword'
                        exact ⟨hlabel, hlocals'⟩
              | continued middleLoop label =>
                  cases wordBodyResult with
                  | normal middleWord | broke middleWord wordLabel =>
                      exact False.elim (by simpa [loopResultMappedToRiscV] using hbodyResult)
                  | continued middleWord wordLabel =>
                      have hlabel : label = wordLabel := by
                        exact hbodyResult.1
                      have hlocals' :
                          loopLocalsMappedToRiscV context middleLoop.locals middleWord :=
                        hbodyResult.2
                      by_cases hzero : label = 0
                      · have hwordLabel : wordLabel = 0 := by
                          exact hlabel.symm.trans hzero
                        subst label
                        subst wordLabel
                        apply ih middleLoop middleWord loopResult wordResult hlocals'
                        · simpa [evalLoopRepeat, hbodyLoop] using hloop
                        · simpa [RiscV.evalWordLoopRepeat, hbodyWord] using hword
                      · have hwordLabel : wordLabel ≠ 0 := by
                          intro hwordZero
                          apply hzero
                          simpa [hwordZero] using hlabel
                        have hloop' :
                            some (.continued middleLoop label) = some loopResult := by
                          simpa [evalLoopRepeat, hbodyLoop, hzero] using hloop
                        have hword' :
                            some (.continued middleWord wordLabel) = some wordResult := by
                          simpa [RiscV.evalWordLoopRepeat, hbodyWord, hwordLabel] using hword
                        cases hloop'
                        cases hword'
                        exact ⟨hlabel, hlocals'⟩
              | returned middleLoop values | raised middleLoop exception =>
                  exact False.elim (by simpa [loopResultMappedToRiscV] using hbodyResult)

theorem bindWordRegisters_single_parameter [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (name : Nat) (value : RiscV.Word width) (register : Fin 32)
    (hregister :
      RiscV.registerOfNat (wordFindVar context name) = some register) :
    RiscV.bindWordRegisters state [wordFindVar context name] [value] =
      some (RiscV.writeRegister (RiscV.clearWordRegisters state) register value) := by
  simp [RiscV.bindWordRegisters, hregister]

theorem loopLocalsMappedToRiscV_single_parameter [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (name : Nat) (value : RiscV.Word width) (register : Fin 32)
    (hregister :
      RiscV.registerOfNat (wordFindVar context name) = some register)
    (hregister_nonzero : register ≠ 0) :
    loopLocalsMappedToRiscV context
      (updateLoopLocal (fun _ => none) name value)
      (RiscV.writeRegister (RiscV.clearWordRegisters state) register value) := by
  intro current currentValue hcurrent
  by_cases hname : current = name
  · subst current
    have hvalue : value = currentValue := by
      simpa [updateLoopLocal] using hcurrent
    subst currentValue
    exact ⟨register, hregister, by
      simp [RiscV.writeRegister, RiscV.readRegister, hregister_nonzero]⟩
  · have : (none : Option (RiscV.Word width)) = some currentValue := by
      simpa [updateLoopLocal, hname] using hcurrent
    simp at this

theorem loopBindParameters_single_parameter_agreement [NeZero width]
    (context : WordContext) (state : RiscV.State width)
    (name : Nat) (value : RiscV.Word width) (register : Fin 32)
    (hregister :
      RiscV.registerOfNat (wordFindVar context name) = some register)
    (hregister_nonzero : register ≠ 0) :
    ∃ locals wordState,
      loopBindParameters [name] [value] (fun _ => none) = some locals ∧
        RiscV.bindWordRegisters state
          [wordFindVar context name] [value] = some wordState ∧
        loopLocalsMappedToRiscV context locals wordState := by
  refine ⟨updateLoopLocal (fun _ => none) name value,
    RiscV.writeRegister (RiscV.clearWordRegisters state) register value,
    ?_, ?_, ?_⟩
  · simp [loopBindParameters]
  · exact bindWordRegisters_single_parameter context state name value register
      hregister
  · exact loopLocalsMappedToRiscV_single_parameter context state name value register
      hregister hregister_nonzero

theorem loopToWord_binop_assign_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : BinOp)
    (destination left right : Nat) (destinationRegister : Fin 32)
    (leftValue rightValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft : loopState.locals left = some leftValue)
    (hright : loopState.locals right = some rightValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.op operator [.var left, .var right]))) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination
          (evalLoopBinOp operator leftValue rightValue)) resultState := by
  intro resultState hresult
  rcases hlocals left leftValue hleft with
    ⟨leftRegister, hleft_register, hleft_value⟩
  rcases hlocals right rightValue hright with
    ⟨rightRegister, hright_register, hright_value⟩
  have hleft_value' : state.registers leftRegister = leftValue := by
    exact hleft_value
  have hright_value' : state.registers rightRegister = rightValue := by
    exact hright_value
  have hand (x y : RiscV.Word width) :
      AndOp.and x y = x &&& y := by
    change x.and y = x &&& y
    exact BitVec.and_eq x y
  have hor (x y : RiscV.Word width) :
      OrOp.or x y = x ||| y := by
    change x.or y = x ||| y
    exact BitVec.or_eq x y
  have hxor (x y : RiscV.Word width) :
      HXor.hXor x y = x ^^^ y := by
    rfl
  cases operator <;>
    simp [loopToWordProg, wordCompileExp,
      wordCompileExp.wordCompileExpList] at hresult <;>
    simp [RiscV.evalWordProg, RiscV.wordExpToInstructions,
      RiscV.wordExpToInstruction, RiscV.executeInstructions,
      hdestination, hleft_register, hright_register] at hresult
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .add leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hleft_register, hright_register,
        hleft_value', hright_value', evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .sub leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hleft_register, hright_register,
        hleft_value', hright_value', evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .and leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hleft_register, hright_register,
        hleft_value', hright_value', hand, evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .or leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hleft_register, hright_register,
        hleft_value', hright_value', hor, evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value
  · subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      have hvalue : evalLoopBinOp .xor leftValue rightValue = current := by
        simpa [updateLoopLocal, evalLoopBinOp] using hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hleft_register, hright_register,
        hleft_value', hright_value', hxor, evalLoopBinOp]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value

theorem loopToWord_shift_assign_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : Shift)
    (destination left right : Nat) (destinationRegister : Fin 32)
    (leftValue rightValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft : loopState.locals left = some leftValue)
    (hright : loopState.locals right = some rightValue)
    (hright_bounded : rightValue.toNat < width)
    (hoperator : operator = .lsl ∨ operator = .lsr)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.shift operator (.var left) (.var right)))) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination
          (match operator with
          | .lsl => ShiftLeft.shiftLeft leftValue rightValue
          | .lsr => ShiftRight.shiftRight leftValue rightValue
          | .asr => leftValue
          | .ror => leftValue)) resultState := by
  rcases hoperator with rfl | rfl
  all_goals
    intro resultState hresult
    rcases hlocals left leftValue hleft with
      ⟨leftRegister, hleft_register, hleft_value⟩
    rcases hlocals right rightValue hright with
      ⟨rightRegister, hright_register, hright_value⟩
    have hleft_value' : state.registers leftRegister = leftValue := by
      exact hleft_value
    have hright_value' : state.registers rightRegister = rightValue := by
      exact hright_value
    have hright_amount :
        RiscV.shiftAmount rightValue = rightValue.toNat := by
      simp [RiscV.shiftAmount, Nat.mod_eq_of_lt hright_bounded]
    have hshiftLeft (x y : RiscV.Word width) :
        ShiftLeft.shiftLeft x y = x <<< y.toNat := by
      rfl
    have hshiftRight (x y : RiscV.Word width) :
        ShiftRight.shiftRight x y = x >>> y.toNat := by
      rfl
    simp [loopToWordProg, wordCompileExp,
      wordCompileExp.wordCompileExpList] at hresult
    simp [RiscV.evalWordProg, RiscV.wordExpToInstructions,
      RiscV.wordExpToInstruction, RiscV.executeInstructions,
      hdestination, hleft_register, hright_register] at hresult
    subst resultState
    intro name current hcurrent
    by_cases hname : name = destination
    · subst name
      simp [updateLoopLocal] at hcurrent
      subst current
      refine ⟨destinationRegister, hdestination, ?_⟩
      simp [updateLoopLocal, RiscV.execute, RiscV.writeRegister,
        RiscV.readRegister, hdestination_nonzero, hleft_register,
        hright_register, hleft_value', hright_value', hright_amount,
        hshiftLeft, hshiftRight]
    · have hcurrent' : loopState.locals name = some current := by
        simpa [updateLoopLocal, hname] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hregister_nonalias := hnoalias name hname register hregister
      simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
        hdestination_nonzero, hregister_nonalias]
      exact hregister_value

theorem loopToWord_const_assign_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (destination : Nat)
    (value : RiscV.Word width) (destinationRegister : Fin 32)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hzero : RiscV.ZeroRegister state)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.assign destination (.const value))) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination value) resultState := by
  intro resultState hresult
  simp [loopToWordProg, wordCompileExp] at hresult
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  simp [RiscV.evalWordProg, RiscV.wordExpToInstructions,
    RiscV.wordExpToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, hdestination_lt, hdestination_fin] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    have hvalue : value = current := by
      simpa [updateLoopLocal] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.ZeroRegister, RiscV.execute, RiscV.writeRegister,
      RiscV.readRegister, hdestination_nonzero, hzero]
    exact hzero
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, hregister_nonalias]
    exact hregister_value

theorem loopToWord_seq_evaluation_decomposition [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (first second : LoopProg (RiscV.Word width))
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (hloop :
      evalLoopProg 2 loopState (.seq first second) =
        some (.normal finalLoop))
    (hword :
      RiscV.evalWordProg state (loopToWordProg context (.seq first second)) =
        some finalWord) :
    ∃ middleLoop middleWord,
      evalLoopProg 1 loopState first = some (.normal middleLoop) ∧
        evalLoopProg 1 middleLoop second = some (.normal finalLoop) ∧
        RiscV.evalWordProg state (loopToWordProg context first) =
          some middleWord ∧
        RiscV.evalWordProg middleWord (loopToWordProg context second) =
          some finalWord := by
  cases hfirst : evalLoopProg 1 loopState first with
  | none =>
      simp [evalLoopProg, hfirst] at hloop
  | some firstResult =>
      cases firstResult with
      | normal middleLoop =>
          have hsecond :
              evalLoopProg 1 middleLoop second = some (.normal finalLoop) := by
            simpa [evalLoopProg, hfirst] using hloop
          cases hwordFirst :
              RiscV.evalWordProg state (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, RiscV.evalWordProg, hwordFirst] at hword
          | some middleWord =>
              have hwordSecond :
                  RiscV.evalWordProg middleWord
                    (loopToWordProg context second) = some finalWord := by
                simpa [loopToWordProg, RiscV.evalWordProg, hwordFirst] using hword
              exact ⟨middleLoop, middleWord, rfl, hsecond,
                rfl, hwordSecond⟩
      | returned middleLoop values =>
          simp [evalLoopProg, hfirst] at hloop
      | broke middleLoop label =>
          simp [evalLoopProg, hfirst] at hloop
      | continued middleLoop label =>
          simp [evalLoopProg, hfirst] at hloop
      | raised middleLoop exception =>
          simp [evalLoopProg, hfirst] at hloop

theorem loopToWord_seq_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (first second : LoopProg (RiscV.Word width))
    (finalLoop : LoopState (RiscV.Word width))
    (finalWord : RiscV.State width)
    (hloop :
      evalLoopProg 2 loopState (.seq first second) =
        some (.normal finalLoop))
    (hword :
      RiscV.evalWordProg state (loopToWordProg context (.seq first second)) =
        some finalWord)
    (hfirst :
      ∀ middleLoop middleWord,
        evalLoopProg 1 loopState first = some (.normal middleLoop) →
        RiscV.evalWordProg state (loopToWordProg context first) =
          some middleWord →
        loopLocalsMappedToRiscV context middleLoop.locals middleWord)
    (hsecond :
      ∀ middleLoop middleWord,
        loopLocalsMappedToRiscV context middleLoop.locals middleWord →
        ∀ finalLoop finalWord,
          evalLoopProg 1 middleLoop second = some (.normal finalLoop) →
          RiscV.evalWordProg middleWord (loopToWordProg context second) =
            some finalWord →
          loopLocalsMappedToRiscV context finalLoop.locals finalWord) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  rcases loopToWord_seq_evaluation_decomposition context loopState state
      first second finalLoop finalWord hloop hword with
    ⟨middleLoop, middleWord, hfirst_loop, hsecond_loop,
      hfirst_word, hsecond_word⟩
  exact hsecond middleLoop middleWord
    (hfirst middleLoop middleWord hfirst_loop hfirst_word)
    finalLoop finalWord hsecond_loop hsecond_word

theorem loopToWord_condition_agreement_of_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : Cmp) (condition : Nat)
    (right : RegImm (RiscV.Word width))
    (leftValue rightValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft : loopState.locals condition = some leftValue)
    (hright : (match right with
      | .imm value => some value
      | .reg name => loopState.locals name) = some rightValue)
    (hoperator : operator = .equal ∨ operator = .notEqual ∨
      operator = .lower ∨ operator = .notLower ∨
      operator = .test ∨ operator = .notTest) :
    evalLoopCondition operator leftValue rightValue =
      RiscV.evalWordCondition state operator (wordFindVar context condition)
        (wordRegImm context right) := by
  rcases hlocals condition leftValue hleft with
    ⟨conditionRegister, hcondition_register, hcondition_value⟩
  have hand (x y : RiscV.Word width) :
      AndOp.and x y = x &&& y := by
    change x.and y = x &&& y
    exact BitVec.and_eq x y
  cases right with
  | imm immediate =>
      have hright_value : immediate = rightValue := by
        simpa using hright
      subst rightValue
      rcases hoperator with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [evalLoopCondition, RiscV.evalWordCondition, wordRegImm,
          hcondition_register, hcondition_value, hand]
  | reg name =>
      have hright_local : loopState.locals name = some rightValue := by
        simpa using hright
      rcases hlocals name rightValue hright_local with
        ⟨rightRegister, hright_register, hright_value⟩
      rcases hoperator with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [evalLoopCondition, RiscV.evalWordCondition, wordRegImm,
          hcondition_register, hright_register, hcondition_value,
        hright_value, hand]

theorem loopToWord_ite_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : Cmp) (condition : Nat)
    (right : RegImm (RiscV.Word width))
    (thenBranch elseBranch : LoopProg (RiscV.Word width))
    (live : List Nat) (leftValue rightValue : RiscV.Word width)
    (choose : Bool)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft : loopState.locals condition = some leftValue)
    (hright : (match right with
      | .imm value => some value
      | .reg name => loopState.locals name) = some rightValue)
    (hchooseLoop : evalLoopCondition operator leftValue rightValue = some choose)
    (hchooseWord : RiscV.evalWordCondition state operator
        (wordFindVar context condition) (wordRegImm context right) = some choose)
    (hthen : ∀ middleLoop middleWord,
      evalLoopProg 1 loopState thenBranch = some (.normal middleLoop) →
      RiscV.evalWordProg state (loopToWordProg context thenBranch) = some middleWord →
      loopLocalsMappedToRiscV context middleLoop.locals middleWord)
    ( helse : ∀ middleLoop middleWord,
      evalLoopProg 1 loopState elseBranch = some (.normal middleLoop) →
      RiscV.evalWordProg state (loopToWordProg context elseBranch) = some middleWord →
      loopLocalsMappedToRiscV context middleLoop.locals middleWord) :
    ∀ finalLoop finalWord,
      evalLoopProg 2 loopState
          (.ite operator condition right thenBranch elseBranch live) =
        some (.normal finalLoop) →
      RiscV.evalWordProg state
          (loopToWordProg context
            (.ite operator condition right thenBranch elseBranch live)) =
        some finalWord →
      loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  cases choose with
  | false =>
      intro finalLoop finalWord hloop hword
      have helse_loop :
          evalLoopProg 1 loopState elseBranch = some (.normal finalLoop) := by
        cases right <;> simp_all [evalLoopProg, hchooseLoop]
      cases hmiddle : RiscV.evalWordProg state (loopToWordProg context elseBranch) with
      | none =>
          cases right <;>
            simp_all [loopToWordProg, RiscV.evalWordProg, hmiddle]
      | some middleWord =>
          have helse_word :
              RiscV.evalWordProg state (loopToWordProg context elseBranch) =
                some middleWord := hmiddle
          have htick : RiscV.evalWordProg middleWord
              (.tick : WordProg (RiscV.Word width)) = some finalWord := by
            cases right <;>
              simp_all [loopToWordProg, RiscV.evalWordProg, hmiddle]
          exact loopToWord_tick_preserves_mapped_locals context finalLoop.locals
            middleWord (helse finalLoop middleWord helse_loop helse_word) finalWord htick
  | true =>
      intro finalLoop finalWord hloop hword
      have hthen_loop :
          evalLoopProg 1 loopState thenBranch = some (.normal finalLoop) := by
        cases right <;> simp_all [evalLoopProg, hchooseLoop]
      cases hmiddle : RiscV.evalWordProg state (loopToWordProg context thenBranch) with
      | none =>
          cases right <;>
            simp_all [loopToWordProg, RiscV.evalWordProg, hmiddle]
      | some middleWord =>
          have hthen_word :
              RiscV.evalWordProg state (loopToWordProg context thenBranch) =
                some middleWord := hmiddle
          have htick : RiscV.evalWordProg middleWord
              (.tick : WordProg (RiscV.Word width)) = some finalWord := by
            cases right <;>
              simp_all [loopToWordProg, RiscV.evalWordProg, hmiddle]
          exact loopToWord_tick_preserves_mapped_locals context finalLoop.locals
            middleWord (hthen finalLoop middleWord hthen_loop hthen_word) finalWord htick

theorem loopToWord_loop_break_exec [NeZero width] (state : RiscV.State width) :
    RiscV.evalWordLoopProg 6 state
        (loopToWordProg ({ vars := [] } : WordContext)
          (.loop [] (.break 0) [])) =
      some (.normal (RiscV.execute (RiscV.execute state (.addi 0 0 0))
        (.addi 0 0 0))) := by
  simp [loopToWordProg, RiscV.evalWordLoopProg, RiscV.evalWordLoopRepeat,
    RiscV.evalWordProg, RiscV.execute, RiscV.writeRegister, RiscV.nextPc]

theorem loopToWord_div_assign_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (destination dividend divisor : Nat)
    (destinationRegister : Fin 32)
    (dividendValue divisorValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hdividend : loopState.locals dividend = some dividendValue)
    (hdivisor : loopState.locals divisor = some divisorValue)
    (hdivisor_nonzero : divisorValue ≠ 0)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.arith (.div destination dividend divisor))) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination
          (dividendValue / divisorValue)) resultState := by
  intro resultState hresult
  rcases hlocals dividend dividendValue hdividend with
    ⟨dividendRegister, hdividend_register, hdividend_value⟩
  rcases hlocals divisor divisorValue hdivisor with
    ⟨divisorRegister, hdivisor_register, hdivisor_value⟩
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have hdividend_lt : wordFindVar context dividend < 32 :=
    RiscV.registerOfNat_some_lt hdividend_register
  have hdivisor_lt : wordFindVar context divisor < 32 :=
    RiscV.registerOfNat_some_lt hdivisor_register
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  have hdividend_fin :
      (⟨wordFindVar context dividend, hdividend_lt⟩ : Fin 32) =
        dividendRegister := by
    have h := hdividend_register
    simp [RiscV.registerOfNat, hdividend_lt] at h
    exact h
  have hdivisor_fin :
      (⟨wordFindVar context divisor, hdivisor_lt⟩ : Fin 32) =
        divisorRegister := by
    have h := hdivisor_register
    simp [RiscV.registerOfNat, hdivisor_lt] at h
    exact h
  simp [loopToWordProg, wordArith] at hresult
  simp [RiscV.evalWordProg, RiscV.wordArithToInstructions,
    RiscV.wordArithToInstruction, RiscV.executeInstructions,
    RiscV.registerOfNat, hdestination_lt, hdividend_lt, hdivisor_lt,
    hdestination_fin, hdividend_fin, hdivisor_fin] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    simp [updateLoopLocal] at hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    have hdividend_value' :
        state.registers dividendRegister = dividendValue := by
      exact hdividend_value
    have hdivisor_value' :
        state.registers divisorRegister = divisorValue := by
      exact hdivisor_value
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, hdividend_register, hdivisor_register,
      hdividend_value', hdivisor_value', hdivisor_nonzero,
      BitVec.udiv_def]
    intro hzero
    exact (hdivisor_nonzero hzero).elim
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, hregister_nonalias]
    exact hregister_value

theorem loopToWord_locValue_preserves_mapped_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (destination source : Nat)
    (destinationRegister sourceRegister : Fin 32)
    (sourceValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hsource : loopState.locals source = some sourceValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hsource_register :
      RiscV.registerOfNat (wordFindVar context source) =
        some sourceRegister)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hnoalias :
      ∀ name, name ≠ destination →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ destinationRegister) :
    ∀ resultState,
      RiscV.evalWordProg state
        (loopToWordProg context (.locValue destination source)) =
        some resultState →
      loopLocalsMappedToRiscV context
        (updateLoopLocal loopState.locals destination sourceValue) resultState := by
  intro resultState hresult
  rcases hlocals source sourceValue hsource with
    ⟨mappedSourceRegister, hsource_map, hsource_value⟩
  have hsource_map_eq : mappedSourceRegister = sourceRegister := by
    simpa [hsource_register] using hsource_map.symm
  subst mappedSourceRegister
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have hsource_lt : wordFindVar context source < 32 :=
    RiscV.registerOfNat_some_lt hsource_register
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  have hsource_fin :
      (⟨wordFindVar context source, hsource_lt⟩ : Fin 32) =
        sourceRegister := by
    have h := hsource_register
    simp [RiscV.registerOfNat, hsource_lt] at h
    exact h
  simp [loopToWordProg, RiscV.evalWordProg,
    RiscV.wordExpToInstructions, RiscV.wordExpToInstruction,
    RiscV.executeInstructions, RiscV.registerOfNat, hdestination_lt,
    hsource_lt, hdestination_fin, hsource_fin] at hresult
  subst resultState
  intro name current hcurrent
  by_cases hname : name = destination
  · subst name
    simp [updateLoopLocal] at hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, hsource_value]
    exact hsource_value
  · have hcurrent' : loopState.locals name = some current := by
      simpa [updateLoopLocal, hname] using hcurrent
    rcases hlocals name current hcurrent' with
      ⟨register, hregister, hregister_value⟩
    refine ⟨register, hregister, ?_⟩
    have hregister_nonalias := hnoalias name hname register hregister
    simp [RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
      hdestination_nonzero, hregister_nonalias]
    exact hregister_value

theorem loopToWord_binop_assign_agreement_of_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : BinOp)
    (destination left right : Nat) (destinationRegister : Fin 32)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft_present : ∃ value, loopState.locals left = some value)
    (hright_present : ∃ value, loopState.locals right = some value)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 loopState
      (.assign destination (.op operator [.var left, .var right]))).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.op operator [.var left, .var right])))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  cases hleft : loopState.locals left with
  | none =>
      obtain ⟨value, hvalue⟩ := hleft_present
      simp [hleft] at hvalue
  | some leftValue =>
      cases hright : loopState.locals right with
      | none =>
          obtain ⟨value, hvalue⟩ := hright_present
          simp [hright] at hvalue
      | some rightValue =>
          rcases hlocals left leftValue hleft with
            ⟨leftRegister, hleft_register, hleft_value⟩
          rcases hlocals right rightValue hright with
            ⟨rightRegister, hright_register, hright_value⟩
          have hleft_value' : state.registers leftRegister = leftValue := by
            exact hleft_value
          have hright_value' : state.registers rightRegister = rightValue := by
            exact hright_value
          have hand (x y : RiscV.Word width) :
              AndOp.and x y = x &&& y := by
            change x.and y = x &&& y
            exact BitVec.and_eq x y
          have hor (x y : RiscV.Word width) :
              OrOp.or x y = x ||| y := by
            change x.or y = x ||| y
            exact BitVec.or_eq x y
          have hxor (x y : RiscV.Word width) :
              HXor.hXor x y = x ^^^ y := by
            rfl
          cases operator <;>
            simp [evalLoopProg, evalLoopExp, evalLoopBinOp, loopToWordProg,
              wordCompileExp, wordCompileExp.wordCompileExpList,
              RiscV.evalWordProg, RiscV.wordExpToInstructions,
              RiscV.wordExpToInstruction, RiscV.executeInstructions,
              RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
              RiscV.nextPc, updateLoopLocal, hleft, hright,
              hleft_register, hright_register, hleft_value, hright_value,
              hleft_value', hright_value',
              hdestination, hdestination_nonzero, hand, hor, hxor]

theorem loopToWord_shift_assign_agreement_of_locals [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width) (operator : Shift)
    (destination left right : Nat) (destinationRegister : Fin 32)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals state)
    (hleft_present : ∃ value, loopState.locals left = some value)
    (hright_present : ∃ value, loopState.locals right = some value)
    (hright_bounded :
      ∀ value, loopState.locals right = some value → value.toNat < width)
    (hoperator : operator = .lsl ∨ operator = .lsr)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hdestination_nonzero : destinationRegister ≠ 0) :
    (evalLoopProg 1 loopState
      (.assign destination (.shift operator (.var left) (.var right)))).bind
        (fun result =>
          match result with
          | .normal state => state.locals destination
          | _ => none) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.assign destination (.shift operator (.var left) (.var right))))).map
        (fun state => RiscV.readRegister state destinationRegister) := by
  cases hleft : loopState.locals left with
  | none =>
      obtain ⟨value, hvalue⟩ := hleft_present
      simp [hleft] at hvalue
  | some leftValue =>
      cases hright : loopState.locals right with
      | none =>
          obtain ⟨value, hvalue⟩ := hright_present
          simp [hright] at hvalue
      | some rightValue =>
          rcases hlocals left leftValue hleft with
            ⟨leftRegister, hleft_register, hleft_value⟩
          rcases hlocals right rightValue hright with
            ⟨rightRegister, hright_register, hright_value⟩
          have hleft_value' : state.registers leftRegister = leftValue := by
            exact hleft_value
          have hright_value' : state.registers rightRegister = rightValue := by
            exact hright_value
          have hright_amount :
              RiscV.shiftAmount rightValue = rightValue.toNat := by
            simp [RiscV.shiftAmount,
              Nat.mod_eq_of_lt (hright_bounded rightValue hright)]
          have hshiftLeft (x y : RiscV.Word width) :
              ShiftLeft.shiftLeft x y = x <<< y.toNat := by
            rfl
          have hshiftRight (x y : RiscV.Word width) :
              ShiftRight.shiftRight x y = x >>> y.toNat := by
            rfl
          rcases hoperator with rfl | rfl <;>
            simp [evalLoopProg, evalLoopExp, evalLoopShift, loopToWordProg,
              wordCompileExp, wordCompileExp.wordCompileExpList,
              RiscV.evalWordProg, RiscV.wordExpToInstructions,
              RiscV.wordExpToInstruction, RiscV.executeInstructions,
              RiscV.execute, RiscV.writeRegister, RiscV.readRegister,
              RiscV.nextPc, updateLoopLocal, hleft, hright,
              hleft_register, hright_register, hleft_value, hright_value,
              hleft_value', hright_value', hdestination,
              hdestination_nonzero, hright_amount,
              hshiftLeft, hshiftRight,
              RiscV.bitVecWordShiftLeft, RiscV.bitVecWordShiftRight]

end Flapjack
