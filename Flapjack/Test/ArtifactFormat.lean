import Flapjack.RiscV.ArtifactFormat

/-!
# RISC-V artifact-format regressions

The reference format is the complete assembler emitted by CakeML's
`cake --pancake --target=riscv` command.  These checks deliberately cover the
serialization boundary only: instruction/register bytes are tested elsewhere
and remain independent of the ABI parity work.
-/

namespace Flapjack.Test.ArtifactFormat

open Flapjack Flapjack.RiscV

def sampleBytes : List (BitVec 8) :=
  (List.range 17).map (BitVec.ofNat 8)

#guard hexByteUpper (BitVec.ofNat 8 0xab) == "0xAB"
#guard hexByteUpper (BitVec.ofNat 8 0x04) == "0x04"

#guard assemblyByteLines sampleBytes ==
  [ "\t.byte 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F",
    "\t.byte 0x10" ]

#guard sectionSymbolName [] 0 == "cml__Raise_4"
#guard sectionSymbolName [] 1 == "cml_generated_main_6"
#guard runtimeSectionSymbolName [] 0 == "cml__Raise_4"
#guard runtimeSectionSymbolName [] 1 == "cml__StoreConsts_5"
#guard runtimeSectionSymbolName [] 2 == "cml__GC_3"
#guard runtimeSectionSymbolName [] 3 == "cml_generated_main_6"

def bitmapCall : CrepProg Nat :=
  .call (some ([], none)) "f" []

#guard crepBitmapCallEntries bitmapCall = 1
#guard crepBitmapCallEntries (.seq bitmapCall bitmapCall) = 2

def hasAll (needles lines : List String) : Bool :=
  needles.all (fun needle => lines.contains needle)

def pancakeEnvelopeMarkers : List String :=
  [ "     .file        \"cake.S\"",
    "     .data",
    "cake_bitmaps:",
    "#### Start up code",
    "cdecl(cml_main):",
    "#### CakeML FFI interface (each block is 16 bytes long)",
    "cake_main:",
    "#### Generated machine code follows",
    "cdecl(cake_codebuffer_begin):",
    "cdecl(cake_codebuffer_end):" ]

def pancakeEnvelopeMatches : Bool :=
  hasAll pancakeEnvelopeMarkers
    (pancakeAssembly [] [] |>.splitOn "\n")

#guard pancakeEnvelopeMatches

def pancakePrologueMatches : Bool :=
  pancakePrologue.take 4 ==
    [ "/* Preprocessor to get around Mac OS, Windows, and Linux differences in naming and calling conventions */",
      "", "#if defined(__APPLE__)", "# define cdecl(s) _##s" ]

#guard pancakePrologueMatches

/-! CakeML's `code_buffer_def` and `preamble` (`cakeml/compiler/backend/exportScript.sml`
    lines 68-69 and 88-100) fix the runtime buffers at `DATA_BUFFER_SIZE` 65536 and
    `CODE_BUFFER_SIZE` 5242880 and lay the code buffer out as
    `.space CODE_BUFFER_SIZE` / `.p2align 12` / `.space 4096`.  The guest's generated
    code is under a megabyte, far below both constants, so there is no 4 MB output
    truncation in this pipeline; these checks pin the port to the reference frame. -/

def cakeBufferDefines : List String :=
  ["#define DATA_BUFFER_SIZE    65536", "#define CODE_BUFFER_SIZE  5242880"]

def pancakeBufferDefinesMatch : Bool :=
  cakeBufferDefines.all (fun line => pancakePrologue.contains line)

#guard pancakeBufferDefinesMatch

def codeBufferExpected : List String :=
  ["     .globl cdecl(cake_codebuffer_begin)",
   "cdecl(cake_codebuffer_begin):",
   "#if defined(EVAL)",
   "     .space CODE_BUFFER_SIZE",
   "#endif",
   "     .p2align 12",
   "     .globl cdecl(cake_codebuffer_end)",
   "cdecl(cake_codebuffer_end):",
   "     .space 4096"]

def dropUntil (needle : String) : List String → List String
  | [] => []
  | line :: lines => if line == needle then line :: lines else dropUntil needle lines

def pancakeCodeBufferMatches : Bool :=
  (dropUntil "     .globl cdecl(cake_codebuffer_begin)"
      (pancakeAssembly [] [] |>.splitOn "\n")).take codeBufferExpected.length ==
    codeBufferExpected

#guard pancakeCodeBufferMatches

end Flapjack.Test.ArtifactFormat
