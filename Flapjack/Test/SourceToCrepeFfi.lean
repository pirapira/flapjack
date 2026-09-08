import Flapjack.CrepeCorrectness
import Flapjack.RiscV.Model

/-!
Source-to-full-Crepe FFI regression.

The source handler writes the local named `result`; the compiled handler writes
its declared Crepe slot.  The comparison observes both resulting locals after
the compiler-generated temporary declarations have been restored.
-/

namespace Flapjack

def sourceToCrepeFfiContext : CompileContext (RiscV.Word 64) :=
  { vars := [("result", (.one, [1]))], functions := [], exceptions := [],
    maxVar := 1, bytesInWord := BitVec.ofNat 64 8 }

def sourceToCrepeFfiProgram : Prog (RiscV.Word 64) :=
  .extCall "inc" (.const (BitVec.ofNat 64 41)) (.const 0)
    (.const 0) (.const 0)

def sourceToCrepeFfiState : CrepState (RiscV.Word 64) :=
  { locals := fun name => if name = 1 then some (BitVec.ofNat 64 0) else none
    memory := fun _ => none }

def sourceToCrepeFfiPrimitive : CrepPrimitiveHandler (RiscV.Word 64) :=
  fun _ _ => none

def sourceToCrepeFfiHandler : CrepFfiHandler (RiscV.Word 64) :=
  fun function configuration _ _ _ state =>
    if function == "inc" then
      some { state with
        locals := updateCrepLocal state.locals 1 (configuration + 1) }
    else none

def sourceToCrepeFfiSharedMem : CrepSharedMemHandler (RiscV.Word 64) :=
  defaultCrepSharedMemHandler

def sourceToCrepeFfiSourceHandler : PanFfiHandler (RiscV.Word 64) :=
  fun function configuration _ _ _ locals =>
    if function == "inc" then
      some (updatePanLocal locals "result" (configuration + 1))
    else none

def sourceToCrepeFfiSourceLocals : VarName → Option (RiscV.Word 64) :=
  fun name => if name == "result" then some 0 else none

#guard
    (evalCrepFullProg [] sourceToCrepeFfiPrimitive sourceToCrepeFfiHandler
      sourceToCrepeFfiSharedMem 0 100 30 sourceToCrepeFfiState
      (compileProg sourceToCrepeFfiContext sourceToCrepeFfiProgram)).map (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) =
      (evalPanFfiProg sourceToCrepeFfiSourceHandler
        sourceToCrepeFfiSourceLocals sourceToCrepeFfiProgram).map
          (fun locals => locals "result")

#guard
    (evalCrepFullProg [] sourceToCrepeFfiPrimitive sourceToCrepeFfiHandler
      sourceToCrepeFfiSharedMem 0 100 30 sourceToCrepeFfiState
      (compileProg sourceToCrepeFfiContext sourceToCrepeFfiProgram)).map (fun result =>
        match result with
        | .normal state => state.locals 1
        | _ => none) = some (some (BitVec.ofNat 64 42))

end Flapjack
