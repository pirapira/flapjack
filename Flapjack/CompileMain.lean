import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.RiscV.ArtifactFormat

/-!
# Flapjack compiler command

This command-line wrapper exposes the checked source-facing RV64I pipeline as
a Pancake-compatible assembly frame, raw bytes, or linked sections.  Assembly
is the default and `--assembly` is retained as a compatibility alias for
`--pancake`; code and layout differences remain tracked by the parity beads.
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

inductive OutputFormat where
  | pancake
  | hex
  | sections
  deriving DecidableEq

def usage : String :=
  "Usage: lake exe flapjack-compile [--assembly|--pancake|--hex|--sections] " ++
  "[SOURCE.pnk]\nRead Pancake source from SOURCE.pnk or stdin. The default, " ++
  "--assembly, and --pancake modes emit the Pancake-compatible assembly " ++
  "frame; --hex emits the legacy lowercase byte line; --sections emits " ++
  "<label> <address> <bytes> lines."

def parseArguments (arguments : List String) : IO (Option (OutputFormat × Option String)) := do
  match arguments with
  | [] =>
      pure (some (.pancake, none))
  | [argument] =>
      if argument == "--help" || argument == "-h" then
        IO.println usage
        pure none
      else if argument == "--assembly" || argument == "--pancake" then
        pure (some (.pancake, none))
      else if argument == "--hex" then
        pure (some (.hex, none))
      else if argument == "--sections" then
        pure (some (.sections, none))
      else
        pure (some (.pancake, some argument))
  | [format, argument] =>
      let outputFormat ←
        if format == "--assembly" || format == "--pancake" then pure .pancake
        else if format == "--hex" then pure .hex
        else if format == "--sections" then pure .sections
        else do
          IO.eprintln s!"flapjack-compile: unknown option {format}\n{usage}"
          IO.Process.exit 2
      pure (some (outputFormat, some argument))
  | _ =>
      IO.eprintln s!"flapjack-compile: expected at most one input path\n{usage}"
      IO.Process.exit 2

def readSource (path : Option String) : IO String := do
  match path with
  | none =>
      let stdin ← IO.getStdin
      pure (← stdin.readToEnd)
  | some argument => IO.FS.readFile argument

def printSections (sections : List (RiscV.EncodedRiscVSection width)) : IO Unit := do
  for entry in sections do
    IO.println (s!"{entry.label} {entry.address.toNat} " ++ hexBytes entry.bytes)

def compileMain (arguments : List String) : IO UInt32 := do
  let some (outputFormat, path) ← parseArguments arguments | return 0
  let source ← readSource path
  if outputFormat == .pancake then
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
            match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
                (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] compileRemoveConfig
                "main" source with
            | .ok image =>
                for warning in image.warnings do
                  IO.eprintln s!"warning: {repr warning}"
                IO.print (RiscV.pancakeRuntimeAssembly pipeline.crepe image)
                return 0
            | .error error =>
                IO.eprintln s!"flapjack-compile: {repr error}"
                return 1
  else if outputFormat == .sections then
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
