import Flapjack.RiscV.PipelineDiagnostics

/-!
# Flapjack compiler command

This is the command-line wrapper for the currently supported source-facing
RV64I pipeline.  It deliberately emits the checked byte artifact rather than
claiming to emit CakeML's complete assembly/runtime image.
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
  "Usage: lake exe flapjack-compile [SOURCE.pnk]\n" ++
  "Read Pancake source from SOURCE.pnk or stdin and emit RV64I bytes as " ++
  "space-separated lowercase hexadecimal."

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
  let some source ← readSource arguments | return 0
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
