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
