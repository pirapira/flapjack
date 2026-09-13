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
    "cml__Raise_4"
  else if label == 1 then
    "cml_generated_main_6"
  else
    match crepe[label - 1]? with
    | some function => s!"cml_{sanitizeSymbolName function.name}_{label + 5}"
    | none => s!"cml_section_{label + 5}"

def assemblyByteLines (values : List (BitVec 8)) : List String :=
  (List.range ((values.length + 15) / 16)).map (fun line =>
    let chunk := (values.drop (line * 16)).take 16
    "\t.byte " ++ String.intercalate "," (chunk.map hexByteUpper))

def assemblySymbolLines (crepe : List (CompiledFunction (RiscV.Word 64))) :
    Nat → List (RiscV.EncodedRiscVSection 64) → List String
  | _, [] => []
  | offset, encoded :: rest =>
      s!"    makesym({sectionSymbolName crepe encoded.label}, {offset}, {encoded.bytes.length})" ::
        (if encoded.label == 0 then
          s!"    makesym(cml__StoreConsts_5, {offset + encoded.bytes.length}, 0)" ::
            assemblySymbolLines crepe (offset + encoded.bytes.length) rest
        else
          assemblySymbolLines crepe (offset + encoded.bytes.length) rest)

def assemblyRuntimeSymbolLines :
    List (RiscV.EncodedRiscVSection 64) → List String
  | [] =>
      ["    makesym(cml__Init_0, 0, 0)",
       "    makesym(cml__Halt0_1, 0, 0)",
       "    makesym(cml__Halt2_2, 0, 0)",
       "    makesym(cml__GC_3, 0, 0)"]
  | _ :: _ =>
      ["    makesym(cml__Init_0, 0, 0)",
       "    makesym(cml__Halt0_1, 0, 0)",
       "    makesym(cml__Halt2_2, 0, 0)",
       "    makesym(cml__GC_3, 0, 0)"]

def pancakePrologue : List String :=
  ["/* Preprocessor to get around Mac OS, Windows, and Linux differences in naming and calling conventions */",
   "", "#if defined(__APPLE__)", "# define cdecl(s) _##s", "#else",
   "# define cdecl(s) s", "#endif", "", "#if defined(__APPLE__)",
   "# define wcdecl(s) _##s", "#elif defined(__WIN32)",
   "# define wcdecl(s) windows_##s", "#else", "# define wcdecl(s) s", "#endif",
   "", "#if defined(__APPLE__)", "# define wcml(s) s", "#elif defined(__WIN32)",
   "# define wcml(s) windows_##s", "#else", "# define wcml(s) s", "#endif", "",
   "#if defined(__APPLE__)", ".macro _makesym name, base, len",
   ".set \\name, cake_main+\\base", ".endm",
   "# define makesym(name,base,len) _makesym name, base, len",
   "#elif defined(__WIN32)", ".macro _makesym name, base, len",
   ".set \\name, cake_main+\\base", ".endm",
   "# define makesym(name,base,len) _makesym name, base, len", "#else",
   ".macro _makesym name, base, len", ".local \\name",
   ".set \\name, cake_main+\\base", ".size \\name, \\len",
   ".type \\name, function", ".endm",
   "# define makesym(name,base,len) _makesym name, base, len", "#endif", "",
   "#define DATA_BUFFER_SIZE    65536", "#define CODE_BUFFER_SIZE  5242880"]

def pancakeAssembly (crepe : List (CompiledFunction (RiscV.Word 64)))
    (sections : List (RiscV.EncodedRiscVSection 64)) : String :=
  let bytes := sections.flatMap (fun encoded => encoded.bytes)
  String.intercalate "\n"
    (pancakePrologue ++
      ["", "     .file        \"cake.S\"", "", "     .data",
       "     .p2align 3", "cdecl(cml_heap): .quad 0",
       "cdecl(cml_stack): .quad 0", "cdecl(cml_stackend): .quad 0",
       "     .p2align 3", "cake_bitmaps:", "\t.quad 4",
       "     .globl cdecl(cake_bitmaps_buffer_begin)",
       "cdecl(cake_bitmaps_buffer_begin):", "#if defined(EVAL)",
       "     .space DATA_BUFFER_SIZE", "#endif",
       "     .globl cdecl(cake_bitmaps_buffer_end)",
       "cdecl(cake_bitmaps_buffer_end):", "", "#### Start up code", "",
       "     .text", "     .p2align 3", "     .globl  cdecl(cml_main)",
       "     .globl  cdecl(cml_heap)", "     .globl  cdecl(cml_stack)",
       "     .globl  cdecl(cml_stackend)", "     .type   cml_main, function",
       "cdecl(cml_main):", "     la      a0,cake_main",
       "     ld      a1,cdecl(cml_heap)",
       "     ld      a2,cdecl(cml_stack)",
       "     ld      a3,cdecl(cml_stackend)", "     j       cake_main", "",
       "#### CakeML FFI interface (each block is 16 bytes long)", "",
       "     .p2align 4", "cake_clear:", "     tail cdecl(cml_exit)",
       "     .p2align 4", "cake_exit:", "     tail cdecl(cml_exit)",
       "     .p2align 4", "cake_main:", "", "#### Generated machine code follows"]
      ++ assemblyByteLines bytes
      ++ ["", "     .globl cdecl(cake_codebuffer_begin)",
          "cdecl(cake_codebuffer_begin):", "#if defined(EVAL)",
          "     .space CODE_BUFFER_SIZE", "#endif", "     .p2align 12",
          "     .globl cdecl(cake_codebuffer_end)",
          "cdecl(cake_codebuffer_end):", "     .space 4096"]
      ++ assemblyRuntimeSymbolLines sections
      ++ assemblySymbolLines crepe 0 sections
      ++ [""])

end Flapjack.RiscV
