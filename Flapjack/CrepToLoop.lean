import Flapjack.Loop
import Flapjack.Static
import Flapjack.RiscV.Model

/-!
Initial Crepe-to-Loop lowering for the direct executable fragment. This keeps
the IR close to CakeML's `crep_to_loopScript.sml`; expression side effects,
condition materialization, liveness, and arithmetic expansion are subsequent
passes.
-/

namespace Flapjack

structure LoopContext (α : Type u) where
  vars : InfoMap Nat
  functions : InfoMap (Nat × Nat)
  maxVar : Nat
  target : RiscV.Architecture
  deriving Repr

def findLoopVar (context : LoopContext α) (name : VarName) : Nat :=
  match lookupInfo name context.vars with
  | some value => value
  | none => 0

def lowerLoopExp : CrepExp α → LoopExp α
  | .const value => .const value
  | .var name => .var name
  | .load address => .load (lowerLoopExp address)
  | .load32 address => .load (lowerLoopExp address)
  | .loadByte address => .load (lowerLoopExp address)
  | .loadGlob address => .lookup address
  | .op operator arguments => .op operator (arguments.map lowerLoopExp)
  | .crepOp operator arguments => .crepOp operator (arguments.map lowerLoopExp)
  | .cmp operator left right => .cmp operator (lowerLoopExp left) (lowerLoopExp right)
  | .shift operator left right => .shift operator (lowerLoopExp left) (lowerLoopExp right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr
termination_by expression => sizeOf expression

def lowerLoopProg : CrepProg α → LoopProg α
  | .skip => .skip
  | .dec name value body =>
      .seq (.assign name (lowerLoopExp value)) (lowerLoopProg body)
  | .assign name value => .assign name (lowerLoopExp value)
  | .primitive names operator arguments => .primitive names operator arguments
  | .store _ _ => .fail
  | .store32 _ _ => .fail
  | .storeByte _ _ => .fail
  | .storeGlob address value => .setGlobal address (lowerLoopExp value)
  | .seq first second => .seq (lowerLoopProg first) (lowerLoopProg second)
  | .break label => .break label
  | .continue label => .continue label
  | .raise _ => .fail
  | .return _ => .fail
  | .shMem operator name address => .shMem operator name (lowerLoopExp address)
  | .tick => .tick
  | .call _ _ _ => .fail
  | .extCall function configuration configurationLength array arrayLength =>
      .ffi function configuration configurationLength array arrayLength []
  | .ite _ _ _ => .fail
  | .while _ _ => .fail
termination_by program => sizeOf program

theorem lowerLoopProg_skip :
    lowerLoopProg (.skip : CrepProg α) = .skip := by
  simp [lowerLoopProg]

theorem lowerLoopProg_seq (first second : CrepProg α) :
    lowerLoopProg (.seq first second) =
      .seq (lowerLoopProg first) (lowerLoopProg second) := by
  simp [lowerLoopProg]

end Flapjack
