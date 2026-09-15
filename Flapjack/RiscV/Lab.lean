import Flapjack.Lab
import Flapjack.StackAlloc
import Flapjack.StackAlloc.Runtime
import Flapjack.RiscV.Ffi
import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.CakeStackReseat
import Flapjack.RiscV.LongDivRuntime

/-!
# LabLang to RISC-V

This module is the first concrete assembler boundary after StackLang
flattening. It computes byte positions for local labels, resolves symbolic
jumps, and lowers the LabLang operations supported by the current RISC-V
model. Unsupported target operations fail through Option rather than being
silently emitted.
-/

namespace Flapjack.RiscV

/-! CakeML's `riscv_ast (Inst (Const r i))` uses three exact constant
    materialization cases.  Keep the arithmetic here in `Nat` so the same
    instruction-selection function can also provide the instruction count
    needed while resolving Lab labels.  The emitted immediates are still
    width-indexed words at the final instruction boundary. -/

def labConst32 {width : Nat} [NeZero width]
    (destination : Fin 32) (value : Nat) :
    List (Instruction width) :=
  let low32 := value % 2 ^ 32
  let high20 := low32 / 2 ^ 12
  let low12 := low32 % 2 ^ 12
  if low12 / 2 ^ 11 % 2 = 1 then
    [.lui destination (BitVec.ofNat width ((2 ^ 20 - 1) - high20)),
      .xori destination destination (BitVec.ofNat width low12)]
  else
    [.lui destination (BitVec.ofNat width high20),
      .addi destination destination (BitVec.ofNat width low12)]

def labConstInstructions {width : Nat} [NeZero width]
    (destination zero temporary : Fin 32) (value : Nat) :
    List (Instruction width) :=
  if value < 2 ^ 11 then
    [.ori destination zero (BitVec.ofNat width value)]
  else
    let modulus := 2 ^ width
    let normalized := value % modulus
    let low12 := normalized % 2 ^ 12
    let fitsImm12 :=
      normalized ==
        (if low12 / 2 ^ 11 % 2 = 0 then
          low12
        else
          (modulus - (2 ^ 12 - low12)) % modulus)
    if fitsImm12 then
      [.ori destination zero (BitVec.ofNat width low12)]
    else
      let low32 := normalized % 2 ^ 32
      let high32 := normalized / 2 ^ 32 % 2 ^ 32
      let low32Sign := low32 / 2 ^ 31 % 2 = 1
      let fitsSigned32 :=
        (high32 = 0 ∧ !low32Sign) ||
          (high32 = 2 ^ 32 - 1 ∧ low32Sign)
      if fitsSigned32 then
        labConst32 destination low32
      else if low32Sign then
        labConst32 temporary low32 ++
          labConst32 destination ((2 ^ 32 - 1) - high32) ++
          [.slli destination destination (BitVec.ofNat width 32),
            .xor destination destination temporary]
      else
        labConst32 temporary low32 ++
          labConst32 destination high32 ++
          [.slli destination destination (BitVec.ofNat width 32),
            .or destination destination temporary]

def labConstInstructionCount (value : Nat) : Nat :=
  if value < 2 ^ 11 then 1
  else
    let normalized := value % 2 ^ 64
    let low12 := normalized % 2 ^ 12
    let fitsImm12 :=
      normalized ==
        (if low12 / 2 ^ 11 % 2 = 0 then
          low12
        else
          (2 ^ 64 - (2 ^ 12 - low12)) % 2 ^ 64)
    if fitsImm12 then 1
    else
      let low32 := normalized % 2 ^ 32
      let high32 := normalized / 2 ^ 32 % 2 ^ 32
      let low32Sign := low32 / 2 ^ 31 % 2 = 1
      let fitsSigned32 :=
        (high32 = 0 ∧ !low32Sign) ||
          (high32 = 2 ^ 32 - 1 ∧ low32Sign)
      if fitsSigned32 then 2 else 6

def labConditionPreludeCount (operator : Cmp)
    (right : WordRegImm (Word width)) : Nat :=
  match right with
  | .reg _ => match operator with | .test | .notTest => 1 | _ => 0
  | .imm value =>
      if value == 0 then
        match operator with | .test | .notTest => 1 | _ => 0
      else 1

def labLineInstructionCount : LabLine (Word width) → Nat
  | .label _ _ _ => 0
  | .asm operation _ _ =>
      match operation with
      | .shift .ror _ _ _ => 5
      | .word (.arith (.longMul _ _ _ _)) => 2
      | .word (.arith (.addCarry _ _ _ _ _)) => 6
      | .word (.arith (.cakeAddCarry _ _ _ _)) => 6
      | .const _ value => labConstInstructionCount value
      | .arithImm _ destination left immediate =>
          if destination = left && immediate = 0 then 0 else 1
      | .tick => 0
      | _ => 1
  | .labAsm operation _ _ =>
      match operation with
      | .jump _ | .call _ | .locValue _ _ | .linkValue _ | .return | .install | .halt => 1
      | .jumpCmp operator _ right _ => 1 + labConditionPreludeCount operator right
      | .callFfi _ => 1
      | .heapAlloc _ => 1

def labFfiStubOffset [NeZero width] (context : WordFfiContext)
    (function : FunName) (position : Nat) : Option (Word width) := do
  let index ← lookupWordFfiIndex function context.services
  /- CakeML emits FFI blocks in reverse `ffi_names` order.  The target
     assembler therefore addresses service index `i` at the fixed prefix
     distance `(3 + i) * ffi_offset`: two runtime blocks (cake_clear and
     cake_exit), followed by the reversed service table. -/
  let stubDistance := 3 + index
  pure (0 - BitVec.ofNat width (position + stubDistance * 16))

def labCollectLabels (_sectionId : Nat) (position : Nat) :
    List (LabLine (Word width)) → List (Nat × Nat)
  | [] => []
  | .label _ label _ :: lines =>
      (label, position) :: labCollectLabels _sectionId position lines
  | line :: lines =>
      labCollectLabels _sectionId
        (position + 4 * labLineInstructionCount line) lines

def labLookupPosition (label : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (candidate, position) :: labels =>
      if label == candidate then some position
      else labLookupPosition label labels

def labResolveRef (sectionId : Nat) (labels : List (Nat × Nat)) (ref : LabRef) :
    Option Nat :=
  if ref.sectionId == sectionId then labLookupPosition ref.label labels
  else none

def labOffset [NeZero width] (target position : Nat) : Word width :=
  if target >= position then
    BitVec.ofNat width (target - position)
  else
    0 - BitVec.ofNat width (position - target)

def labBranch [NeZero width] (operator : Cmp) (left right : Fin 32)
    (offset : Word width) : Instruction width :=
  match operator with
  | .equal => .branchNe left right offset
  | .notEqual => .branchEq left right offset
  | .less => .branchGe left right offset
  | .notLess => .branchLt left right offset
  | .lower => .branchGeU left right offset
  | .notLower => .branchLtU left right offset
  | .test => .branchNe left right offset
  | .notTest => .branchEq left right offset

def labBinOpInstruction [NeZero width] (operator : BinOp)
    (destination left right : Nat) : Option (Instruction width) := do
  let destination ← labRegisterOfNat (portToStack destination)
  let left ← labRegisterOfNat (portToStack left)
  let right ← labRegisterOfNat (portToStack right)
  pure (match operator with
    | .add => .add destination left right
    | .sub => .sub destination left right
    | .and => .and destination left right
    | .or => .or destination left right
    | .xor => .xor destination left right)

def labShiftInstructions [NeZero width] (operator : Shift)
    (destination left right : Nat) : Option (List (Instruction width)) := do
  if operator == .ror &&
      [destination, left, right].any (· == 31) then
    none
  else
    let destination ← labRegisterOfNat (portToStack destination)
    let left ← labRegisterOfNat (portToStack left)
    let right ← labRegisterOfNat (portToStack right)
    match operator with
    | .lsl => pure [.sll destination left right]
    | .lsr => pure [.srl destination left right]
    | .asr => pure [.sra destination left right]
    | .ror => do
        let zero ← labRegisterOfNat (portToStack portZeroRegister)
        pure [
          .ori 31 zero (BitVec.ofNat width width),
          .sub 31 31 right,
          .sll 31 left 31,
          .srl destination left right,
          .or destination destination 31]

def labCompilePlain [NeZero width] :
    LabPlain (Word width) → Option (List (Instruction width))
  | .word (.arith operation) => wordArithToInstructions operation
  | .word (.const destination value) =>
      labCompilePlain (.const destination value.toNat)
  | .word (.binop operator destination source (.imm value)) => do
      let destination ← labRegisterOfNat (portToStack destination)
      let source ← labRegisterOfNat (portToStack source)
      match operator with
      | .add => pure [.addi destination source value]
      | .sub => pure [.addi destination source (0 - value)]
      | .and => pure [.andi destination source value]
      | .or => pure [.ori destination source value]
      | .xor => pure [.xori destination source value]
  | .word (.binop operator destination source (.reg name)) =>
      (labBinOpInstruction operator destination source name).map List.singleton
  | .word (.shiftInst operator destination source (.imm value)) => do
      let destination ← labRegisterOfNat (portToStack destination)
      let source ← labRegisterOfNat (portToStack source)
      match operator with
      | .lsl => pure [.slli destination source value]
      | .lsr => pure [.srli destination source value]
      | .asr => pure [.srai destination source value]
      | .ror => none
  | .word (.shiftInst operator destination source (.reg name)) =>
      labShiftInstructions operator destination source name
  | .word instruction => (wordInstToInstruction instruction).map List.singleton
  | .const destination value => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let destination ← labRegisterOfNat (portToStack destination)
      if value < 2 ^ 11 then
        pure [.ori destination zero (BitVec.ofNat width value)]
      else
        let temporary ← labRegisterOfNat (portToStack 31)
        pure (labConstInstructions destination zero temporary value)
  | .arith operator destination left right =>
      (labBinOpInstruction operator destination left right).map List.singleton
  | .arithImm operator destination left immediate => do
      if destination == left && immediate == 0 then
        pure []
      else
        let destination ← labRegisterOfNat (portToStack destination)
        let left ← labRegisterOfNat (portToStack left)
        match operator with
        | .add => pure [.addi destination left (BitVec.ofNat width immediate)]
        | .sub => pure [.addi destination left (0 - BitVec.ofNat width immediate)]
        | .and | .or | .xor => none
  | .shift operator destination left right =>
      labShiftInstructions operator destination left right
  | .tick =>
      -- CakeML's lab_filter removes the `Inst Skip` generated for Tick
      -- before assembling the final artifact.  Keeping this line at zero
      -- width is important: subsequent local-label positions must not count
      -- an instruction that is not emitted.
      pure []
  | .jumpReg register => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let register ← labRegisterOfNat (portToStack register)
      pure [.jalr zero register zero]
  | .shareMem operator register address =>
      wordShareInstToInstructions operator register (.var address)
  | .codeBufferWrite address value =>
      (wordInstToInstruction (.mem .store8 value address)).map List.singleton
  | .dataBufferWrite address value =>
      (wordInstToInstruction (.mem .store value address)).map List.singleton

/-! StackLang's `LocValue` uses register 0 as the conventional link
    register.  The port's ordinary register fields are hardware-numbered, so
    this special carrier must be translated separately; sending port register
    0 through `portToStack` would select the architectural zero register and
    silently discard FFI/install return addresses. -/
def labLocValueRegister (register : Nat) : Option (Fin 32) :=
  if register = 0 then
    labRegisterOfNat (portToStack portLinkRegister)
  else
    labRegisterOfNat (portToStack register)

def labCompileAsm [NeZero width] (context : WordFfiContext)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat) :
    LabAsm (Word width) → Option (List (Instruction width))
  | .jump target => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let target ← labResolveRef sectionId labels target
      pure [.jal zero (labOffset target position)]
  | .call target => do
      let link ← labRegisterOfNat (portToStack portLinkRegister)
      let target ← labResolveRef sectionId labels target
      pure [.jal link (labOffset target position)]
  | .locValue register target => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let register ← labLocValueRegister register
      let target ← labResolveRef sectionId labels target
      pure [.addi register zero (BitVec.ofNat width target)]
  | .linkValue target => do
      let link ← labRegisterOfNat (portToStack portLinkRegister)
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let target ← labResolveRef sectionId labels target
      pure [.addi link zero (BitVec.ofNat width target)]
  | .return => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let link ← labRegisterOfNat (portToStack portLinkRegister)
      pure [.jalr zero link 0]
  | .jumpCmp operator condition right target => do
      let (left, right, prelude) ← wordConditionOperands operator condition right
      let target ← labResolveRef sectionId labels target
      let branchPosition := position + 4 * prelude.length
      pure (prelude ++ [labBranch operator left right
        (labOffset target branchPosition)])
  | .callFfi function => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let offset ← labFfiStubOffset context function position
      pure [.jal zero offset]
  | .install =>
      pure [.jal 0 (0 - BitVec.ofNat width (position + 2 * 16))]
  | .heapAlloc _ => none
  | .halt => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      pure [.jal zero (0 - BitVec.ofNat width (position + 16))]

def labCompileLines [NeZero width] (context : WordFfiContext)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat) :
    List (LabLine (Word width)) → Option (List (Instruction width))
  | [] => some []
  | .label _ _ _ :: lines =>
      labCompileLines context sectionId labels position lines
  | .asm operation _ _ :: lines => do
      let code ← labCompilePlain operation
      let rest ← labCompileLines context sectionId labels
        (position + 4 * labLineInstructionCount (.asm operation [] 0)) lines
      pure (code ++ rest)
  | .labAsm operation _ _ :: lines => do
      let code ← labCompileAsm context sectionId labels position operation
      let rest ← labCompileLines context sectionId labels
        (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) lines
      pure (code ++ rest)

def compileLabSection [NeZero width] (context : WordFfiContext)
    (sectionData : LabSection (Word width)) : Option (List (Instruction width)) :=
  let labels := labCollectLabels sectionData.name 0 sectionData.lines
  labCompileLines context sectionData.name labels 0 sectionData.lines

/-! The first executable StackLang-to-RISC-V composition.  StackRemove lowers
    the stack and runtime-store operations, LabLang flattens the remaining
    control flow, and this boundary selects concrete RISC-V instructions. -/
def compileStackProgramToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel : Nat) (program : StackProg (Word width)) :
    Option (List (Instruction width)) :=
  compileLabSection context
    (labProgramToSectionAfterStackRemove config sectionId initialLabel program)

/-! The current concrete Word-to-Stack compiler uses `Nat` for constants,
    while the target backend uses width-indexed words.  Since only conditional
    immediates carry the StackProg type parameter, this adapter is deliberately
    small and explicit. -/
def labAsmNatToWord [NeZero width] : LabAsm Nat → LabAsm (Word width)
  | .jump target => .jump target
  | .jumpCmp operator condition (.imm value) target =>
      .jumpCmp operator condition (.imm (BitVec.ofNat width value)) target
  | .jumpCmp operator condition (.reg register) target =>
      .jumpCmp operator condition (.reg register) target
  | .call target => .call target
  | .locValue register target => .locValue register target
  | .linkValue target => .linkValue target
  | .return => .return
  | .callFfi function => .callFfi function
  | .heapAlloc words => .heapAlloc words
  | .install => .install
  | .halt => .halt

def labRegImmNatToWord [NeZero width] : WordRegImm Nat → WordRegImm (Word width)
  | .reg name => .reg name
  | .imm value => .imm (BitVec.ofNat width value)

def labWordInstNatToWord [NeZero width] : WordInst Nat → WordInst (Word width)
  | .arith operation => .arith operation
  | .mem operator destination address => .mem operator destination address
  | .const destination value =>
      .const destination (BitVec.ofNat width value)
  | .binop operator destination source right =>
      .binop operator destination source (labRegImmNatToWord right)
  | .shiftInst operator destination source amount =>
      .shiftInst operator destination source (labRegImmNatToWord amount)
  | .memOffset operator destination base offset =>
      .memOffset operator destination base (BitVec.ofNat width offset)

def labPlainNatToWord [NeZero width] : LabPlain Nat → LabPlain (Word width)
  | .word instruction => .word (labWordInstNatToWord instruction)
  | .const destination value => .const destination value
  | .arith operator destination left right =>
      .arith operator destination left right
  | .arithImm operator destination left immediate =>
      .arithImm operator destination left immediate
  | .shift operator destination left right =>
      .shift operator destination left right
  | .tick => .tick
  | .jumpReg register => .jumpReg register
  | .codeBufferWrite address value => .codeBufferWrite address value
  | .dataBufferWrite address value => .dataBufferWrite address value
  | .shareMem operator register address =>
      .shareMem operator register address

def labLineNatToWord [NeZero width] : LabLine Nat → LabLine (Word width)
  | .label sectionId label length => .label sectionId label length
  | .asm operation bytes length =>
      .asm (labPlainNatToWord operation) bytes length
  | .labAsm operation bytes length =>
      .labAsm (labAsmNatToWord operation) bytes length

def labSectionNatToWord [NeZero width] (sectionData : LabSection Nat) :
    LabSection (Word width) :=
  { name := sectionData.name
    lines := sectionData.lines.map labLineNatToWord }

def compileLabSectionNat [NeZero width] (context : WordFfiContext)
    (sectionData : LabSection Nat) : Option (List (Instruction width)) :=
  compileLabSection context (labSectionNatToWord sectionData)

def labSectionInstructionCount (sectionData : LabSection (Word width)) : Nat :=
  sectionData.lines.foldl
    (fun count line => count + labLineInstructionCount line) 0

def labCollectProgramLabels (base : Nat) :
    LabProgram (Word width) → List (Nat × Nat × Nat)
  | [] => []
  | sectionData :: sections =>
      let localLabels := labCollectLabels sectionData.name 0 sectionData.lines
      let globalLabels := localLabels.map
        (fun (label, position) => (sectionData.name, label, base + position))
      globalLabels ++ labCollectProgramLabels
        (base + 4 * labSectionInstructionCount sectionData) sections

def labLookupProgramPosition (sectionId label : Nat) :
    List (Nat × Nat × Nat) → Option Nat
  | [] => none
  | (candidateSection, candidateLabel, position) :: labels =>
      if sectionId == candidateSection && label == candidateLabel then some position
      else labLookupProgramPosition sectionId label labels

def labResolveProgramRef (labels : List (Nat × Nat × Nat)) (ref : LabRef) :
    Option Nat :=
  labLookupProgramPosition ref.sectionId ref.label labels

def labCompileAsmProgram [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (position : Nat) :
    LabAsm (Word width) → Option (List (Instruction width))
  | .jump target => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let target ← labResolveProgramRef labels target
      pure [.jal zero (labOffset target position)]
  | .call target => do
      let link ← labRegisterOfNat (portToStack portLinkRegister)
      let target ← labResolveProgramRef labels target
      pure [.jal link (labOffset target position)]
  | .locValue register target => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let register ← labLocValueRegister register
      let target ← labResolveProgramRef labels target
      pure [.addi register zero (BitVec.ofNat width target)]
  | .linkValue target => do
      let link ← labRegisterOfNat (portToStack portLinkRegister)
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let target ← labResolveProgramRef labels target
      pure [.addi link zero (BitVec.ofNat width target)]
  | .return => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let link ← labRegisterOfNat (portToStack portLinkRegister)
      pure [.jalr zero link 0]
  | .jumpCmp operator condition right target => do
      let (left, right, prelude) ← wordConditionOperands operator condition right
      let target ← labResolveProgramRef labels target
      let branchPosition := position + 4 * prelude.length
      pure (prelude ++ [labBranch operator left right
        (labOffset target branchPosition)])
  | .callFfi function => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let offset ← labFfiStubOffset context function position
      pure [.jal zero offset]
  | .install => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      pure [.jal zero (0 - BitVec.ofNat width (position + 2 * 16))]
  | .heapAlloc _ => none
  | .halt => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      pure [.jal zero (0 - BitVec.ofNat width (position + 16))]

def labCompileProgramLines [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (position : Nat) :
    List (LabLine (Word width)) → Option (List (Instruction width))
  | [] => some []
  | .label _ _ _ :: lines =>
      labCompileProgramLines context labels position lines
  | .asm operation _ _ :: lines => do
      let code ← labCompilePlain operation
      let rest ← labCompileProgramLines context labels
        (position + 4 * labLineInstructionCount (.asm operation [] 0)) lines
      pure (code ++ rest)
  | .labAsm operation _ _ :: lines => do
      let code ← labCompileAsmProgram context labels position operation
      let rest ← labCompileProgramLines context labels
        (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) lines
      pure (code ++ rest)

def labCompileProgramSections [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (base : Nat) :
    LabProgram (Word width) → Option (List (Instruction width))
  | [] => some []
  | sectionData :: sections => do
      let code ← labCompileProgramLines context labels base sectionData.lines
      let rest ← labCompileProgramSections context labels
        (base + 4 * labSectionInstructionCount sectionData) sections
      pure (code ++ rest)

def compileLabProgram [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) : Option (List (Instruction width)) :=
  let labels := labCollectProgramLabels 0 program
  labCompileProgramSections context labels 0 program

def compileStackProgramNatToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel : Nat) (program : StackProg Nat) :
    Option (List (Instruction width)) :=
  match stackProgramsWithLongDivRuntime config [(sectionId, program)] with
  | none => none
  | some programs =>
      compileLabProgram context
        ((programs.map (fun (runtimeSection, runtimeProgram) =>
          if runtimeSection = cakeLongDiv1Location ||
              runtimeSection = cakeLongDivLocation then
            labProgramToEntrySection runtimeSection 0 initialLabel
              (stackRemoveComplete config runtimeProgram)
          else
            labProgramToSectionAfterStackRemove config runtimeSection initialLabel
              runtimeProgram)).map labSectionNatToWord)

def compileWordProgramNatToRiscV [NeZero width] [BEq Nat]
    (context : WordFfiContext) (wordConfig : WordStackConfig)
    (removeConfig : StackRemoveConfig) (sectionId initialLabel : Nat)
    (program : WordProg Nat) : Option (List (Instruction width)) := do
  let stackProgram ← wordToStackProgNat wordConfig program
  compileStackProgramNatToRiscV context removeConfig sectionId initialLabel
    stackProgram

def compileWordProgramToRiscV [NeZero width]
    (context : WordFfiContext) (wordConfig : WordStackConfig)
    (removeConfig : StackRemoveConfig) (sectionId initialLabel : Nat)
    (program : WordProg (Word width)) : Option (List (Instruction width)) := do
  let stackProgram ← wordToStackProgWord wordConfig program
  compileStackProgramNatToRiscV context removeConfig sectionId initialLabel
    stackProgram

/-! CakeML's target assembler turns `Halt` into a jump to the target's halt
    PC.  The existing ordinary compiler intentionally rejects that pseudo-op;
    this parallel path computes a halt PC immediately after the linked image,
    emits the jump, and appends a self-loop at that PC. -/
def labCompileAsmWithHalt [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (position _haltPc : Nat) :
    LabAsm (Word width) → Option (List (Instruction width))
  | .jump target => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let target ← labResolveProgramRef labels target
      pure [.jal zero (labOffset target position)]
  | .call target => do
      let link ← labRegisterOfNat (portToStack portLinkRegister)
      let target ← labResolveProgramRef labels target
      pure [.jal link (labOffset target position)]
  | .locValue register target => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let register ← labLocValueRegister register
      let target ← labResolveProgramRef labels target
      pure [.addi register zero (BitVec.ofNat width target)]
  | .linkValue target => do
      let link ← labRegisterOfNat (portToStack portLinkRegister)
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let target ← labResolveProgramRef labels target
      pure [.addi link zero (BitVec.ofNat width target)]
  | .return => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let link ← labRegisterOfNat (portToStack portLinkRegister)
      pure [.jalr zero link 0]
  | .jumpCmp operator condition right target => do
      let (left, right, prelude) ← wordConditionOperands operator condition right
      let target ← labResolveProgramRef labels target
      let branchPosition := position + 4 * prelude.length
      pure (prelude ++ [labBranch operator left right
        (labOffset target branchPosition)])
  | .callFfi function => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let offset ← labFfiStubOffset context function position
      pure [.jal zero offset]
  | .halt => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      pure [.jal zero (0 - BitVec.ofNat width (position + 16))]
  | .install => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      pure [.jal zero (0 - BitVec.ofNat width (position + 2 * 16))]
  | .heapAlloc _ => none

def labCompileProgramLinesWithHalt [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (position haltPc : Nat) :
    List (LabLine (Word width)) → Option (List (Instruction width))
  | [] => some []
  | .label _ _ _ :: lines =>
      labCompileProgramLinesWithHalt context labels position haltPc lines
  | .asm operation _ _ :: lines => do
      let code ← labCompilePlain operation
      let rest ← labCompileProgramLinesWithHalt context labels
        (position + 4 * labLineInstructionCount (.asm operation [] 0)) haltPc lines
      pure (code ++ rest)
  | .labAsm operation _ _ :: lines => do
      let code ← labCompileAsmWithHalt context labels position haltPc operation
      let rest ← labCompileProgramLinesWithHalt context labels
        (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) haltPc lines
      pure (code ++ rest)

def labCompileProgramSectionsWithHalt [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (base haltPc : Nat) :
    LabProgram (Word width) → Option (List (Instruction width))
  | [] => some []
  | sectionData :: sections => do
      let code ← labCompileProgramLinesWithHalt context labels base haltPc
        sectionData.lines
      let rest ← labCompileProgramSectionsWithHalt context labels
        (base + 4 * labSectionInstructionCount sectionData) haltPc sections
      pure (code ++ rest)

def labProgramInstructionCount : LabProgram (Word width) → Nat
  | [] => 0
  | sectionData :: sections =>
      labSectionInstructionCount sectionData + labProgramInstructionCount sections

def compileLabProgramWithHalt [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) : Option (List (Instruction width)) := do
  let labels := labCollectProgramLabels 0 program
  let haltPc := 4 * labProgramInstructionCount program
  let code ← labCompileProgramSectionsWithHalt context labels 0 haltPc program
  pure (code ++ [.jal 0 0])

def executeLabProgramWithHalt [NeZero width] (fuel : Nat)
    (context : WordFfiContext) (program : LabProgram (Word width))
    (state : State width) : Option (State width) :=
  let haltPc := BitVec.ofNat width (4 * labProgramInstructionCount program)
  match compileLabProgramWithHalt context program with
  | some code =>
      executeCodeUntil fuel 0 haltPc code { state with pc := 0 }
  | none => none

/-! A linker result that keeps section entry addresses alongside the flattened
    image. The plain `compileLabProgram` API is convenient for consumers that
    only need code; correctness proofs need the section boundary to initialize
    a function runner at the generated entry address. -/
def compileLabProgramLinkedAux [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (base : Nat) : LabProgram (Word width) →
      Option (List (Nat × Word width × List (Instruction width)))
  | [] => some []
  | sectionData :: sections => do
      let code ← labCompileProgramLines context labels base sectionData.lines
      let rest ← compileLabProgramLinkedAux context labels
        (base + 4 * labSectionInstructionCount sectionData) sections
      pure ((sectionData.name, BitVec.ofNat width base, code) :: rest)

def compileLabProgramLinked [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) :
    Option (List (Nat × Word width × List (Instruction width))) :=
  let labels := labCollectProgramLabels 0 program
  compileLabProgramLinkedAux context labels 0 program

/-! Linked machine images retain CakeML's three-region FFI prefix.  The
service blocks are emitted before `cake_clear` and `cake_exit`, each occupying
one 16-byte block as required by `labFfiStubOffset`.  The executable model
represents the external tail call by materializing the service number, taking
the modeled ECALL, and returning through the continuation in x1; the two fixed
runtime blocks are reserved as non-falling-through placeholders. -/
def labFfiServiceStub [NeZero width] (service : Nat) :
    List (Instruction width) :=
  [.addi 14 0 (BitVec.ofNat width service), .ecall,
   .jalr 0 31 0, .addi 0 0 0]

def labFfiStubPrefix [NeZero width] (context : WordFfiContext) :
    List (Instruction width) :=
  if context.services.isEmpty then []
  else
      context.services.reverse.flatMap (fun (_, service) => labFfiServiceStub service) ++
        List.replicate 8 (.jal 0 0)

/-! A linked FFI call is nested inside an ordinary Cake function call.  Its
    continuation must not overwrite the caller's `x1` link: the service stub
    returns through the reserved scratch `x31`, while the ordinary function
    return still uses `x1`.  Rebase only the linked FFI carrier here; the
    generic Lab flattening contract retains the source `returnAddress` field. -/
def labRebaseLinkedFfiReturnLines [NeZero width] :
    List (LabLine (Word width)) → List (LabLine (Word width))
  | .labAsm (.locValue _ target) bytes length ::
      .labAsm (.callFfi function) callBytes callLength :: lines =>
      .labAsm (.locValue 31 target) bytes length ::
        .labAsm (.callFfi function) callBytes callLength ::
          labRebaseLinkedFfiReturnLines lines
  | line :: lines => line :: labRebaseLinkedFfiReturnLines lines
  | [] => []

def labCompileAsmProgramWithFfiBase [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (position ffiBase : Nat) :
    LabAsm (Word width) → Option (List (Instruction width))
  | .callFfi function => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let offset ← labFfiStubOffset context function (position - ffiBase)
      pure [.jal zero offset]
  | operation => labCompileAsmProgram context labels position operation

def labCompileProgramLinesWithFfiBase [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (position ffiBase : Nat) :
    List (LabLine (Word width)) → Option (List (Instruction width))
  | [] => some []
  | .label _ _ _ :: lines =>
      labCompileProgramLinesWithFfiBase context labels position ffiBase lines
  | .asm operation _ _ :: lines => do
      let code ← labCompilePlain operation
      let rest ← labCompileProgramLinesWithFfiBase context labels
        (position + 4 * labLineInstructionCount (.asm operation [] 0)) ffiBase lines
      pure (code ++ rest)
  | .labAsm operation _ _ :: lines => do
      let code ← labCompileAsmProgramWithFfiBase context labels position ffiBase operation
      let rest ← labCompileProgramLinesWithFfiBase context labels
        (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) ffiBase lines
      pure (code ++ rest)

def compileLabProgramLinkedWithFfiStubsAux [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (base ffiBase : Nat) : LabProgram (Word width) →
      Option (List (Nat × Word width × List (Instruction width)))
  | [] => some []
  | sectionData :: sections => do
      let sectionData :=
        { sectionData with lines := labRebaseLinkedFfiReturnLines sectionData.lines }
      let code ← labCompileProgramLinesWithFfiBase context labels base ffiBase
        sectionData.lines
      let rest ← compileLabProgramLinkedWithFfiStubsAux context labels
        (base + 4 * labSectionInstructionCount sectionData) ffiBase sections
      pure ((sectionData.name, BitVec.ofNat width base, code) :: rest)

def compileLabProgramLinkedWithFfiStubs [NeZero width]
    (context : WordFfiContext) (program : LabProgram (Word width)) :
    Option (List (Nat × Word width × List (Instruction width))) :=
  let stubCode := labFfiStubPrefix context
  let prefixBytes := 4 * stubCode.length
  let labels := labCollectProgramLabels prefixBytes program
  match compileLabProgramLinkedWithFfiStubsAux context labels prefixBytes prefixBytes program with
  | none => none
  | some [] => some []
  | some ((sectionId, _, code) :: sections) =>
      some ((sectionId, 0, stubCode ++ code) :: sections)

def labCompileAsmProgramWithFfiBaseAndHalt [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (position ffiBase haltPc : Nat) :
    LabAsm (Word width) → Option (List (Instruction width))
  | .callFfi function => do
      let zero ← labRegisterOfNat (portToStack portZeroRegister)
      let offset ← labFfiStubOffset context function (position - ffiBase)
      pure [.jal zero offset]
  | operation => labCompileAsmWithHalt context labels position haltPc operation

def labCompileProgramLinesWithFfiBaseAndHalt [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (position ffiBase haltPc : Nat) :
    List (LabLine (Word width)) → Option (List (Instruction width))
  | [] => some []
  | .label _ _ _ :: lines =>
      labCompileProgramLinesWithFfiBaseAndHalt context labels position ffiBase haltPc lines
  | .asm operation _ _ :: lines => do
      let code ← labCompilePlain operation
      let rest ← labCompileProgramLinesWithFfiBaseAndHalt context labels
        (position + 4 * labLineInstructionCount (.asm operation [] 0)) ffiBase haltPc lines
      pure (code ++ rest)
  | .labAsm operation _ _ :: lines => do
      let code ← labCompileAsmProgramWithFfiBaseAndHalt context labels position ffiBase haltPc operation
      let rest ← labCompileProgramLinesWithFfiBaseAndHalt context labels
        (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) ffiBase haltPc lines
      pure (code ++ rest)

def compileLabProgramLinkedWithFfiStubsAndHaltAux [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (base ffiBase haltPc : Nat) : LabProgram (Word width) →
      Option (List (Nat × Word width × List (Instruction width)))
  | [] => some []
  | sectionData :: sections => do
      let code ← labCompileProgramLinesWithFfiBaseAndHalt context labels base ffiBase haltPc
        sectionData.lines
      let rest ← compileLabProgramLinkedWithFfiStubsAndHaltAux context labels
        (base + 4 * labSectionInstructionCount sectionData) ffiBase haltPc sections
      pure ((sectionData.name, BitVec.ofNat width base, code) :: rest)

def compileLabProgramLinkedWithFfiStubsAndHalt [NeZero width]
    (context : WordFfiContext) (program : LabProgram (Word width)) :
    Option (List (Nat × Word width × List (Instruction width))) :=
  let stubCode := labFfiStubPrefix context
  let prefixBytes := 4 * stubCode.length
  let labels := labCollectProgramLabels prefixBytes program
  let haltPc := prefixBytes + 4 * labProgramInstructionCount program
  match compileLabProgramLinkedWithFfiStubsAndHaltAux context labels prefixBytes prefixBytes haltPc program with
  | none => none
  | some [] => some []
  | some ((sectionId, _, code) :: sections) =>
      some ((sectionId, 0, stubCode ++ code) :: sections)

def flattenLabProgramLinked :
    List (Nat × Word width × List (Instruction width)) → List (Instruction width)
  | [] => []
  | (_, _, code) :: sections => code ++ flattenLabProgramLinked sections

theorem compileLabProgramLinkedAux_flatten
    [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (base : Nat)
    (program : LabProgram (Word width)) :
    (compileLabProgramLinkedAux context labels base program).map
        flattenLabProgramLinked =
      labCompileProgramSections context labels base program := by
  induction program generalizing base with
  | nil =>
      simp [compileLabProgramLinkedAux, labCompileProgramSections,
        flattenLabProgramLinked]
  | cons sectionData sections ih =>
      simp only [compileLabProgramLinkedAux, labCompileProgramSections]
      cases hcode : labCompileProgramLines context labels base sectionData.lines with
      | none => simp
      | some code =>
          cases hrest : compileLabProgramLinkedAux context labels
              (base + 4 * labSectionInstructionCount sectionData) sections with
          | none =>
              have hsections := ih
                (base := base + 4 * labSectionInstructionCount sectionData)
              rw [hrest] at hsections
              rw [← hsections]
              simp
          | some rest =>
              have hsections := ih
                (base := base + 4 * labSectionInstructionCount sectionData)
              rw [← hsections]
              simp [hrest, flattenLabProgramLinked]

theorem compileLabProgramLinked_flatten [NeZero width]
    (context : WordFfiContext) (program : LabProgram (Word width)) :
    (compileLabProgramLinked context program).map flattenLabProgramLinked =
      compileLabProgram context program := by
  simp [compileLabProgramLinked, compileLabProgram,
    compileLabProgramLinkedAux_flatten]

def compileLabProgramLinkedWithHaltAux [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (base haltPc : Nat) : LabProgram (Word width) →
      Option (List (Nat × Word width × List (Instruction width)))
  | [] => some []
  | sectionData :: sections => do
      let code ← labCompileProgramLinesWithHalt context labels base haltPc
        sectionData.lines
      let rest ← compileLabProgramLinkedWithHaltAux context labels
        (base + 4 * labSectionInstructionCount sectionData) haltPc sections
      pure ((sectionData.name, BitVec.ofNat width base, code) :: rest)

def compileLabProgramLinkedWithHalt [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) :
    Option (List (Nat × Word width × List (Instruction width))) :=
  let labels := labCollectProgramLabels 0 program
  let haltPc := 4 * labProgramInstructionCount program
  compileLabProgramLinkedWithHaltAux context labels 0 haltPc program

theorem compileLabProgramLinkedWithHaltAux_flatten
    [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (base haltPc : Nat)
    (program : LabProgram (Word width)) :
    (compileLabProgramLinkedWithHaltAux context labels base haltPc program).map
        flattenLabProgramLinked =
      labCompileProgramSectionsWithHalt context labels base haltPc program := by
  induction program generalizing base with
  | nil =>
      simp [compileLabProgramLinkedWithHaltAux, labCompileProgramSectionsWithHalt,
        flattenLabProgramLinked]
  | cons sectionData sections ih =>
      simp only [compileLabProgramLinkedWithHaltAux,
        labCompileProgramSectionsWithHalt]
      cases hcode :
          labCompileProgramLinesWithHalt context labels base haltPc sectionData.lines with
      | none => simp
      | some code =>
          cases hrest : compileLabProgramLinkedWithHaltAux context labels
              (base + 4 * labSectionInstructionCount sectionData) haltPc sections with
          | none =>
              have hsections := ih
                (base := base + 4 * labSectionInstructionCount sectionData)
              rw [hrest] at hsections
              rw [← hsections]
              simp
          | some rest =>
              have hsections := ih
                (base := base + 4 * labSectionInstructionCount sectionData)
              rw [← hsections]
              simp [hrest, flattenLabProgramLinked]

def flattenLabProgramLinkedWithHalt :
    List (Nat × Word width × List (Instruction width)) → List (Instruction width)
  | sections => flattenLabProgramLinked sections ++ [.jal 0 0]

theorem compileLabProgramLinkedWithHalt_flatten [NeZero width]
    (context : WordFfiContext) (program : LabProgram (Word width)) :
    (compileLabProgramLinkedWithHalt context program).map
        flattenLabProgramLinkedWithHalt =
      compileLabProgramWithHalt context program := by
  let labels := labCollectProgramLabels 0 program
  let haltPc := 4 * labProgramInstructionCount program
  change
    (compileLabProgramLinkedWithHaltAux context labels 0 haltPc program).map
        flattenLabProgramLinkedWithHalt =
      (labCompileProgramSectionsWithHalt context labels 0 haltPc program).bind
        (fun code => some (code ++ [.jal 0 0]))
  cases hcompiled : compileLabProgramLinkedWithHaltAux context
      labels 0 haltPc program with
  | none =>
      have hsections := compileLabProgramLinkedWithHaltAux_flatten
        context labels 0 haltPc program
      rw [hcompiled] at hsections
      rw [← hsections]
      simp
  | some sections =>
      have hsections := compileLabProgramLinkedWithHaltAux_flatten
        context labels 0 haltPc program
      rw [hcompiled] at hsections
      rw [← hsections]
      simp [flattenLabProgramLinkedWithHalt]

def compileStackProgramListToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg (Word width))) :
    Option (List (Instruction width)) :=
  compileLabProgram context
    (programs.map (fun (sectionId, program) =>
      labProgramToEntrySection sectionId entryLabel initialLabel
        (stackRemoveComplete config program)))

def compileStackProgramNatListToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  match stackProgramsWithLongDivRuntime config programs with
  | none => none
  | some programs =>
      compileLabProgram context
        ((programs.map (fun (sectionId, program) =>
          if sectionId = cakeLongDiv1Location ||
              sectionId = cakeLongDivLocation then
            labProgramToEntrySection sectionId 0 initialLabel
              (stackRemoveComplete config program)
          else
            labProgramToEntrySection sectionId entryLabel initialLabel
              (stackRemoveComplete config program))).map labSectionNatToWord)

/-! Exception expressions lower to a call to the reserved raise stub at
    section `stackRaiseStubLocation`.  Include that stub in every linked
    image so handler-bearing programs have a concrete target. -/
def compileStackProgramNatListWithRaiseStubToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  compileStackProgramNatListToRiscV context config entryLabel initialLabel
    ((stackRaiseStubLocation, stackRaiseStub false config.addressScratch) :: programs)

def compileStackProgramNatListWithHaltToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  match stackProgramsWithLongDivRuntime config programs with
  | none => none
  | some programs =>
      compileLabProgramWithHalt context
        ((programs.map (fun (sectionId, program) =>
          if sectionId = cakeLongDiv1Location ||
              sectionId = cakeLongDivLocation then
            labProgramToEntrySection sectionId 0 initialLabel
              (stackRemoveComplete config program)
          else
            labProgramToEntrySection sectionId entryLabel initialLabel
              (stackRemoveComplete config program))).map labSectionNatToWord)

/-! StackAlloc-aware composition.  CakeML's allocator pass installs a runtime
    collector stub as a separate section and rewrites heap allocation into a
    call to that section. -/
def compileStackProgramNatListWithStackAllocToRiscV [NeZero width]
    (context : WordFfiContext) (removeConfig : StackRemoveConfig)
    (allocConfig : StackAllocConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  let programs := stackAllocCompile allocConfig programs
  compileStackProgramNatListToRiscV context removeConfig entryLabel initialLabel programs

def compileStackProgramNatListWithSimpleGcToRiscV [NeZero width]
    (context : WordFfiContext) (removeConfig : StackRemoveConfig)
    (allocConfig : StackAllocConfig) (gcConfig : StackGcConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  compileStackProgramNatListWithHaltToRiscV context removeConfig
    entryLabel initialLabel
    (stackAllocCompileWithSimpleGc allocConfig gcConfig programs)

def compileStackProgramNatListWithSimpleGcAndStoreConstsToRiscV [NeZero width]
    (context : WordFfiContext) (removeConfig : StackRemoveConfig)
    (allocConfig : StackAllocConfig) (gcConfig : StackGcConfig)
    (storeConstsLocation registerCount : Nat)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Instruction width)) :=
  compileStackProgramNatListWithHaltToRiscV context removeConfig
    entryLabel initialLabel
    ((stackRaiseStubLocation, stackRaiseStub false removeConfig.addressScratch) ::
      stackAllocCompileWithSimpleGcAndStoreConsts allocConfig gcConfig
        storeConstsLocation registerCount programs)

def compileStackProgramNatListLinkedToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Nat × Word width × List (Instruction width))) :=
  match stackProgramsWithLongDivRuntime config programs with
  | none => none
  | some programs =>
      compileLabProgramLinkedWithFfiStubs context
        ((programs.map (fun (sectionId, program) =>
          if sectionId = cakeLongDiv1Location ||
              sectionId = cakeLongDivLocation then
            labProgramToEntrySection sectionId 0 initialLabel
              (stackRemoveComplete config program)
          else
            labProgramToEntrySection sectionId entryLabel initialLabel
              (stackRemoveComplete config program))).map labSectionNatToWord)

/-! Linked counterpart of the bitmap/simple-GC entry point.  Keeping the
runtime sections in the same Lab linker as ordinary functions preserves their
resolved entry addresses for machine-level correctness harnesses. -/
def compileStackProgramNatListLinkedWithSimpleGcAndStoreConstsToRiscV
    [NeZero width]
    (context : WordFfiContext) (removeConfig : StackRemoveConfig)
    (allocConfig : StackAllocConfig) (gcConfig : StackGcConfig)
    (storeConstsLocation registerCount : Nat)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Nat × Word width × List (Instruction width))) :=
  let programs :=
    (stackRaiseStubLocation, stackRaiseStub false removeConfig.addressScratch) ::
      stackAllocCompileWithSimpleGcAndStoreConsts allocConfig gcConfig
        storeConstsLocation registerCount programs
  match stackProgramsWithLongDivRuntime removeConfig programs with
  | none => none
  | some programs =>
      compileLabProgramLinkedWithFfiStubsAndHalt context
        (((programs.map (fun (sectionId, program) =>
          if sectionId = cakeLongDiv1Location ||
              sectionId = cakeLongDivLocation then
            labProgramToEntrySection sectionId 0 initialLabel
              (stackRemoveComplete removeConfig program)
          else
            labProgramToEntrySection sectionId entryLabel initialLabel
              (stackRemoveComplete removeConfig program))).map labSectionNatToWord))

def compileStackProgramNatListLinkedWithRaiseStubToRiscV [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Nat × Word width × List (Instruction width))) :=
  compileStackProgramNatListLinkedToRiscV context config entryLabel initialLabel
    ((stackRaiseStubLocation, stackRaiseStub false config.addressScratch) :: programs)

theorem labLineInstructionCount_ffi :
    labLineInstructionCount
        (.labAsm (.callFfi "sum") [] 0 : LabLine (Word width)) = 1 := by
  rfl

theorem compileLabSection_ffi [NeZero width] :
    compileLabSection { services := [("sum", 7)] }
      ⟨2, [
        .labAsm (.callFfi "sum") [] 0]⟩ =
      some [.jal 0 (0 - BitVec.ofNat width 48)] := by
  simp [compileLabSection, labCompileLines,
    labCompileAsm, labFfiStubOffset, lookupWordFfiIndex]

theorem compileLabProgram_cross_section_jump [NeZero width] :
    compileLabProgram (width := width) { services := [] }
      [⟨1, [.labAsm (.jump ⟨2, 0⟩) [] 0]⟩,
       ⟨2, [.label 2 0 0, .asm (.const 1 7) [] 0]⟩] =
      some [.jal 0 (BitVec.ofNat width 4),
        .ori 1 0 (BitVec.ofNat width 7)] := by
  have hcount :
      labLineInstructionCount
          (.labAsm (.jump ⟨2, 0⟩) [] 0 : LabLine (Word width)) = 1 := by
    rfl
  simp [compileLabProgram, labCollectProgramLabels,
    labCollectLabels, labSectionInstructionCount, labCompileProgramSections,
    labCompileProgramLines, labCompileAsmProgram,
    labCompilePlain,
    labLookupProgramPosition, labResolveProgramRef,
    labOffset, hcount]

end Flapjack.RiscV
