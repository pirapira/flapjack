import Flapjack.RiscV.PipelineDiagnostics

/-!
# Pancake-compatible RISC-V artifact formatting

The CakeML Pancake RISC-V target writes an assembly source artifact.  In
particular, the machine-code bytes are framed by the runtime data symbols and
the `cake_main` text symbol; each linked code section is also named and given
its offset and size.  Keep this formatter next to the checked image boundary
so the command-line tool does not have to reconstruct section metadata from a
flattened byte list.
-/

namespace Flapjack.RiscV

def pancakeSectionName (label : Nat) : String :=
  if label == 0 then "cml__Raise_0" else s!"cml_section_{label}"

def pancakeByte (value : BitVec 8) : String :=
  let n := value.toNat
  let digit := fun (v : Nat) =>
    if v < 10 then Char.ofNat ('0'.toNat + v)
    else Char.ofNat ('a'.toNat + v - 10)
  s!"0x{digit (n / 16)}{digit (n % 16)}"

def pancakeBytes (values : List (BitVec 8)) : String :=
  String.intercalate ", " (values.map pancakeByte)

def pancakeWords (values : List Nat) : String :=
  String.intercalate ", " (values.map (fun value => s!"{value}"))

def pancakeSection (entry : EncodedRiscVSection width) (offset : Nat) : String :=
  let name := pancakeSectionName entry.label
  let bytes := pancakeBytes entry.bytes
  let payload :=
    if entry.bytes.isEmpty then
      ""
    else
      s!"        .byte {bytes}\n"
  name ++ ":\n" ++ payload ++
    s!"        # address {entry.address.toNat}\n" ++
    s!"        .local {name}\n" ++
    s!"        .set {name}, cake_main+{offset}\n" ++
    s!"        .size {name}, {entry.bytes.length}\n" ++
    s!"        .type {name}, function\n"

def pancakeSections : List (EncodedRiscVSection width) → Nat → String
  | [], _ => ""
  | entry :: sections, offset =>
      pancakeSection entry offset ++
        pancakeSections sections (offset + entry.bytes.length)

def pancakeArtifact (bitmaps : List Nat)
    (sections : List (EncodedRiscVSection width)) : String :=
  "/* Flapjack Pancake-compatible RISC-V artifact */\n" ++
  "     .file        \"flapjack.S\"\n\n" ++
  "     .data\n" ++
  "     .p2align 3\n" ++
  "cml_heap: .quad 0\n" ++
  "cml_stack: .quad 0\n" ++
  "cml_stackend: .quad 0\n" ++
  "     .p2align 3\n" ++
  "cake_bitmaps:\n" ++
  s!"        .quad {pancakeWords bitmaps}\n" ++
  "        .globl cake_bitmaps_buffer_begin\n" ++
  "cake_bitmaps_buffer_begin:\n" ++
  "cake_bitmaps_buffer_end:\n\n" ++
  "#### Start up code\n\n" ++
  "     .text\n" ++
  "     .p2align 3\n" ++
  "     .globl cml_main\n" ++
  "     .type cml_main, function\n" ++
  "cml_main:\n" ++
  "        la a0,cake_main\n" ++
  "        j cake_main\n\n" ++
  "cake_main:\n" ++
  "#### Generated machine code follows\n" ++
  pancakeSections sections 0

def pancakeImage (image : Flapjack.SourceRiscVImage width) : String :=
  pancakeArtifact [4] image.sections

def pancakeRuntimeImage (image : Flapjack.SourceRiscVRuntimeImage width) : String :=
  pancakeArtifact image.bitmaps.data image.sections

end Flapjack.RiscV
