import Flapjack.RiscV.PipelineDiagnostics

/-!
# Flapjack compiler command

This is the command-line wrapper for the currently supported source-facing
RV64I pipeline.  It emits the checked byte artifact, a per-section listing, or
a Cake-style assembly frame (`.text` / `cake_main:` / `.byte` lines /
`makesym(...)` symbol table) so the emitted format can be consumed the same
way as `cake --pancake --target=riscv`.  The assembly mode does not add any
CakeML runtime sections that the port does not produce; the surviving
code/layout differences are tracked separately.
-/

namespace Flapjack

def compileRemoveConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

def hexDigit (value : Nat) : Char :=
  if value < 10 then
    Char.ofNat ('0'.toNat + value)
  else
    Char.ofNat ('a'.toNat + value - 10)

def hexByte (value : BitVec 8) : String :=
  let n := value.toNat
  String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

def hexBytes (values : List (BitVec 8)) : String :=
  String.intercalate " " (values.map hexByte)

def hexDigitUpper (value : Nat) : Char :=
  if value < 10 then
    Char.ofNat ('0'.toNat + value)
  else
    Char.ofNat ('A'.toNat + value - 10)

def hexByteUpper (value : BitVec 8) : String :=
  let n := value.toNat
  String.ofList [hexDigitUpper (n / 16), hexDigitUpper (n % 16)]

def sanitizeSymbolName (name : String) : String :=
  String.ofList (name.toList.filterMap (fun c => if c == '\'' then none else some c))

def sectionSymbolName (crepe : List (CompiledFunction (RiscV.Word 64)))
    (label : Nat) : String :=
  if label == 0 then
    "cml_flapjack_runtime_0"
  else if label == 1 then
    s!"cml_generated_main_1"
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

def assemblyText (crepe : List (CompiledFunction (RiscV.Word 64)))
    (sections : List (RiscV.EncodedRiscVSection 64)) : String :=
  let bytes := sections.flatMap (fun encoded => encoded.bytes)
  String.intercalate "\n" ([".text", ".p2align 3", "cake_main:", ""]
    ++ assemblyByteLines bytes
    ++ assemblySymbolLines crepe 0 sections
    ++ [""])

def usage : String :=
  "Usage: lake exe flapjack-compile [--sections|--assembly] [SOURCE.pnk]\n" ++
  "Read Pancake source from SOURCE.pnk or stdin and emit RV64I bytes as " ++
  "space-separated lowercase hexadecimal.  With --sections, emit one line " ++
  "per linked section as `<label> <address> <bytes>`.  With --assembly, emit " ++
  "a Cake-style assembly frame: a `cake_main:` marker, the linked code image " ++
  "as `.byte` lines, and a `makesym(name, base, len)` symbol table."

def readSource (arguments : List String) : IO (Option String) := do
  match arguments with
  | [] =>
      let stdin ← IO.getStdin
      pure (some (← stdin.readToEnd))
  | [argument] =>
      if argument == "--help" || argument == "-h" then
        IO.println usage
        pure none
      else
        pure (some (← IO.FS.readFile argument))
  | _ =>
      IO.eprintln s!"flapjack-compile: expected zero or one input path\n{usage}"
      IO.Process.exit 2

def compileMain (arguments : List String) : IO UInt32 := do
  let (sectionsMode, assemblyMode, rest) :=
    match arguments with
    | "--sections" :: rest => (true, false, rest)
    | "--assembly" :: rest => (false, true, rest)
    | _ => (false, false, arguments)
  let some source ← readSource rest | return 0
  if assemblyMode then
    match Flapjack.Parser.parseTopDecs (α := RiscV.Word 64)
        (fun value => BitVec.ofInt 64 value) source with
    | .error errors =>
        IO.eprintln s!"flapjack-compile: {repr errors}"
        return 1
    | .ok declarations =>
        match compileFlapjackEntry (α := RiscV.Word 64) .rv64i
            (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
            "main" declarations with
        | none =>
            IO.eprintln "flapjack-compile: entry not found"
            return 1
        | some pipeline =>
            match compileFlapjackRiscVSourceImageChecked (width := 64) .rv64i
                (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] compileRemoveConfig
                "main" source with
            | .ok image =>
                for warning in image.warnings do
                  IO.eprintln s!"warning: {repr warning}"
                IO.println (assemblyText pipeline.crepe image.sections)
                return 0
            | .error error =>
                IO.eprintln s!"flapjack-compile: {repr error}"
                return 1
  else if sectionsMode then
    match compileFlapjackRiscVSourceImageChecked (width := 64) .rv64i
        (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] compileRemoveConfig
        "main" source with
    | .ok image =>
        for warning in image.warnings do
          IO.eprintln s!"warning: {repr warning}"
        for encoded in image.sections do
          IO.println s!"{encoded.label} {encoded.address.toNat} {hexBytes encoded.bytes}"
        return 0
    | .error error =>
        IO.eprintln s!"flapjack-compile: {repr error}"
        return 1
  else
    match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
        (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] compileRemoveConfig
        "main" source with
    | .ok artifact =>
        for warning in artifact.warnings do
          IO.eprintln s!"warning: {repr warning}"
        IO.println (hexBytes artifact.bytes)
        return 0
    | .error error =>
        IO.eprintln s!"flapjack-compile: {repr error}"
        return 1

end Flapjack

def main (arguments : List String) : IO UInt32 := Flapjack.compileMain arguments
