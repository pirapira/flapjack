import Flapjack.RiscV.PipelineDiagnostics

/-!
# Pancake-compatible RISC-V artifact formatting

The Pancake RISC-V target emits an assembly source artifact rather than a
flattened hexadecimal line.  This formatter keeps the target's data/runtime
frame, startup entry, code buffer markers, generated machine-code marker, and
`makesym` section table together.  The byte payload is taken directly from the
checked linked image; no post-processing or hex-to-binary conversion is
needed by parity consumers.
-/

namespace Flapjack.RiscV

def hexDigitUpper (value : Nat) : Char :=
  if value < 10 then
    Char.ofNat ('0'.toNat + value)
  else
    Char.ofNat ('A'.toNat + value - 10)

def hexByteUpper (value : BitVec 8) : String :=
  let n := value.toNat
  String.ofList ['0', 'x', hexDigitUpper (n / 16), hexDigitUpper (n % 16)]

def sanitizeSymbolName (name : String) : String :=
  String.ofList (name.toList.filterMap (fun c => if c == '\'' then none else some c))

def sectionSymbolName (crepe : List (CompiledFunction (RiscV.Word 64)))
    (label : Nat) : String :=
  if label == 0 then
    "cml_flapjack_runtime_0"
  else if label == 1 then
    "cml_generated_main_1"
  else
    match crepe[label - 1]? with
    | some function => s!"cml_{sanitizeSymbolName function.name}_{label}"
    | none => s!"cml_section_{label}"

def assemblyByteLines (values : List (BitVec 8)) : List String :=
  (List.range ((values.length + 15) / 16)).map (fun line =>
    let chunk := (values.drop (line * 16)).take 16
    "\t.byte " ++ String.intercalate "," (chunk.map hexByteUpper))

def assemblySymbolLines (crepe : List (CompiledFunction (RiscV.Word 64))) :
    Nat → List (RiscV.EncodedRiscVSection 64) → List String
  | _, [] => []
  | offset, encoded :: rest =>
      s!"    makesym({sectionSymbolName crepe encoded.label}, {offset}, {encoded.bytes.length})" ::
        assemblySymbolLines crepe (offset + encoded.bytes.length) rest

def pancakeAssembly (crepe : List (CompiledFunction (RiscV.Word 64)))
    (sections : List (RiscV.EncodedRiscVSection 64)) : String :=
  let bytes := sections.flatMap (fun encoded => encoded.bytes)
  String.intercalate "\n"
    (["/* Flapjack Pancake-compatible RISC-V artifact */",
      "     .file        \"flapjack.S\"", "", "     .data",
      "     .p2align 3", "cml_heap: .quad 0", "cml_stack: .quad 0",
      "cml_stackend: .quad 0", "     .p2align 3", "cake_bitmaps:",
      "\t.quad 4", "     .globl cake_bitmaps_buffer_begin",
      "cake_bitmaps_buffer_begin:", "cake_bitmaps_buffer_end:", "",
      "#### Start up code", "", "     .text", "     .p2align 3",
      "     .globl cml_main", "     .globl cml_heap",
      "     .globl cml_stack", "     .globl cml_stackend",
      "     .type cml_main, function", "cml_main:",
      "     la a0,cake_main", "     ld a1,cml_heap",
      "     ld a2,cml_stack", "     ld a3,cml_stackend", "     j cake_main", "",
      "#### CakeML FFI interface (each block is 16 bytes long)", "",
      "     .p2align 4", "cake_main:", "", "#### Generated machine code follows"]
      ++ assemblyByteLines bytes
      ++ ["", "     .globl cake_codebuffer_begin", "cake_codebuffer_begin:",
          "     .p2align 12", "     .globl cake_codebuffer_end",
          "cake_codebuffer_end:", "     .space 4096"]
      ++ assemblySymbolLines crepe 0 sections
      ++ [""])

end Flapjack.RiscV
