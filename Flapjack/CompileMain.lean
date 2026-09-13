import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.RiscV.ArtifactFormat

/-!
# Flapjack compiler command

This is the command-line wrapper for the currently supported source-facing
RV64I pipeline.  Its default output is the Pancake-compatible assembly image;
`--hex` retains the historical raw byte output for low-level consumers.
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
  "Usage: lake exe flapjack-compile [--hex|--sections|--pancake] [SOURCE.pnk]\n" ++
  "Read Pancake source from SOURCE.pnk or stdin and emit a Pancake-compatible " ++
  "RV64I assembly artifact."

def parseArguments (arguments : List String) : IO (Option (OutputFormat × Option String)) := do
  match arguments with
  | [] =>
      pure (some (.pancake, none))
  | [argument] =>
      if argument == "--help" || argument == "-h" then
        IO.println usage
        pure none
      else if argument == "--hex" then
        pure (some (.hex, none))
      else if argument == "--sections" then
        pure (some (.sections, none))
      else if argument == "--pancake" then
        pure (some (.pancake, none))
      else
        pure (some (.pancake, some argument))
  | [format, argument] =>
      let outputFormat ←
        if format == "--hex" then pure .hex
        else if format == "--sections" then pure .sections
        else if format == "--pancake" then pure .pancake
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
    IO.println (s!"{RiscV.pancakeSectionName entry.label} {entry.address.toNat} " ++
      hexBytes entry.bytes)

def compileMain (arguments : List String) : IO UInt32 := do
  let some (outputFormat, path) ← parseArguments arguments | return 0
  let source ← readSource path
  match outputFormat with
  | .hex =>
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
  | .sections =>
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
  | .pancake =>
      match compileFlapjackRiscVSourceImageChecked (width := 64) .rv64i
          (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] compileRemoveConfig
          "main" source with
      | .ok image =>
          for warning in image.warnings do
            IO.eprintln s!"warning: {repr warning}"
          IO.print (RiscV.pancakeImage image)
          return 0
      | .error error =>
          IO.eprintln s!"flapjack-compile: {repr error}"
          return 1

end Flapjack

def main (arguments : List String) : IO UInt32 := Flapjack.compileMain arguments
