import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.RiscV.ArtifactFormat

/-!
# Flapjack compiler command

This command-line wrapper exposes the checked source-facing RV64I pipeline as
raw bytes, linked sections, or a Cake-style assembly frame.  The assembly
mode uses the same `.text`/`cake_main`/`.byte`/`makesym` boundary as
`cake --pancake --target=riscv`; code and layout differences remain tracked by
the parity beads.
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

def usage : String :=
  "Usage: lake exe flapjack-compile [--sections|--assembly] [SOURCE.pnk]\n" ++
  "Read Pancake source from SOURCE.pnk or stdin and emit RV64I bytes as " ++
  "space-separated lowercase hexadecimal.  With --sections, emit one line " ++
  "per linked section as `<label> <address> <bytes>`.  With --assembly, emit " ++
  "the Pancake-compatible data/runtime/startup and code assembly frame."

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

def printSections (sections : List (RiscV.EncodedRiscVSection width)) : IO Unit := do
  for entry in sections do
    IO.println (s!"{entry.label} {entry.address.toNat} " ++ hexBytes entry.bytes)

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
                IO.print (RiscV.pancakeAssembly pipeline.crepe image.sections)
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
        printSections image.sections
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
