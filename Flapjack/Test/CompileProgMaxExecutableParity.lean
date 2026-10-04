import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMax
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
/-! Concrete native RISC-V API fixture. Expected bounds are transcribed from
fresh guarded original source replay; this fixture uses actual native passes and
actual generated frames. The full output/error pair is not replaced by a bound. -/
namespace Flapjack.Test.CompileProgMaxExecutableParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.Basis.Pure.MlString

def backendFixture : Backend.Config where
  sourceConf := ⟨⟨0,0,0⟩, ⟨.bind [] [],.bind [] []⟩, ⟨0⟩, ⟨0,.ln⟩⟩
  closConf := ClosToBvl.defaultConfig
  bvlConf := BvlToBvi.defaultConfig
  dataConf := ⟨0,0,0,0,true,true,false,false,false,false,.none⟩
  wordToWordConf := ⟨0,[]⟩
  wordConf := ⟨0,.ln⟩
  stackConf := ⟨.ln,false,false⟩
  labConf := ⟨.ln,[],0,10,none,[],0⟩
  symbols := []
  tapConf := ⟨false⟩
  exported := []

def machineFixture : MachineConfig 64 Unit Unit where
  progAddresses := fun _ => True
  sharedAddresses := fun _ => False
  ffiEntryPcs := []
  ffiNames := []
  ptrReg := 0
  lenReg := 0
  ptr2Reg := 0
  len2Reg := 0
  ffiInterfer := fun _ _ => ()
  calleeSavedRegs := []
  nextInterfer := fun _ s => s
  haltPc := 0
  ccachePc := 0
  ccacheInterfer := fun _ _ => ()
  target := ⟨Compiler.Encoders.RiscV.Target.riscvConfig,id,fun _ => 0,
    fun _ _ => 0,fun _ _ => 0,fun _ _ => 0,fun _ => true,fun _ _ => ()⟩
  mmioInfo := []

def mainProgram : List (DeclHOL 64) := [.function {
 name := ofString "main",inline := false,exported := false,params := [],
 body := .return (.const 0),returnShape := .one }]

def mkProgram (body : ProgHOL 64) : List (DeclHOL 64) := [.function {
 name := ofString "main",inline := false,exported := false,params := [],
 body := body,returnShape := .one }]

def fDecl : DeclHOL 64 := .function {
  name := ofString "f",inline := false,
  exported := false,params := [],body := .return (.const 7),returnShape := .one}
def callBody : ProgHOL 64 := .decCall (ofString "x") .one (ofString "f") []
 (.return (.var .local (ofString "x")))
def callProgram := mkProgram callBody ++ [fDecl]
def branchProgram := mkProgram (.ite (.const 1) callBody (.return (.const 0))) ++ [fDecl]

/-- Actual original source-replay bounds, not hand-selected frame inputs. -/
def runChecks : IO Bool := do
  let cases : List (String × List (DeclHOL 64) × Option Nat) := [
    ("empty",[],none), ("leaf",mainProgram,some 0),
    ("tail_recursive",mkProgram (.call none (ofString "main") []),some 0),
    ("call_leaf",callProgram,some 5), ("branch",branchProgram,some 5),
    ("missing",mkProgram (.call none (ofString "missing") []),none),
    ("recursive",mkProgram (.decCall (ofString "x") .one (ofString "main") []
      (.return (.var .local (ofString "x")))),none)]
  for (name,program,expected) in cases do
    unless (compileProgMaxExecutable backendFixture machineFixture program).2 == expected do
      throw (IO.userError ("original compileProgMax bound mismatch: " ++ name))
  let asm := machineFixture.target.config
  let wp := (WordToWord.compileExecutable backendFixture.wordToWordConf asm
    (panToWordCompileProgHOL asm.isa callProgram)).2
  let (_,wc,fs,_) := WordToStack.Native.compileNative asm false wp
  unless fs == [0,0,2,0] && sptToAList wc.stackFrameSize == [(65,2),(64,0),(66,0)] do
    throw (IO.userError "original compileProgMax generated frames mismatch")
  IO.println "PASS callable compileProgMax: 7 original native pipeline bound cases"
  return true

end Flapjack.Test.CompileProgMaxExecutableParity
