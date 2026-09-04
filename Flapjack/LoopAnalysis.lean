import Flapjack.CrepToLoop

/-!
Structural analyses for the Loop language. These are the list-based
counterparts of CakeML's `loop_live` inputs; a later pass can replace the
lists with a finite-set representation without changing the syntax layer.
-/

namespace Flapjack

def loopVarsOfExp : LoopExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .lookup _ => []
  | .load address => loopVarsOfExp address
  | .op _ arguments => arguments.flatMap loopVarsOfExp
  | .crepOp _ arguments => arguments.flatMap loopVarsOfExp
  | .cmp _ left right => loopVarsOfExp left ++ loopVarsOfExp right
  | .shift _ left right => loopVarsOfExp left ++ loopVarsOfExp right
  | .baseAddr => []
  | .topAddr => []

def loopAssignedVars : LoopProg α → List Nat
  | .skip => []
  | .assign name _ => [name]
  | .primitive destinations _ _ => destinations
  | .arith operation =>
      match operation with
      | .longMul left right _ _ => [left, right]
      | .longDiv left right _ _ _ => [left, right]
      | .div destination _ _ => [destination]
  | .load32 _ destination => [destination]
  | .loadByte _ destination => [destination]
  | .seq first second => loopAssignedVars first ++ loopAssignedVars second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopAssignedVars thenBranch ++ loopAssignedVars elseBranch
  | .locValue destination _ => [destination]
  | .shMem _ destination _ => [destination]
  | .mark body => loopAssignedVars body
  | .loop _ body _ => loopAssignedVars body
  | .call none _ _ _ => []
  | .call (some (returns, _)) _ _ none => returns
  | .call (some (returns, _)) _ _ (some (exception, handler, normal, _)) =>
      returns ++ exception :: loopAssignedVars handler ++ loopAssignedVars normal
  | _ => []

def loopInsert (name : Nat) (names : List Nat) : List Nat :=
  if name ∈ names then names else name :: names

def loopInsertAll : List Nat → List Nat → List Nat
  | [], names => names
  | name :: rest, names => loopInsert name (loopInsertAll rest names)

def loopAccVars : LoopProg α → List Nat → List Nat
  | .seq first second, names => loopAccVars first (loopAccVars second names)
  | .break _, names => names
  | .continue _, names => names
  | .loop _ body _, names => loopAccVars body names
  | .ite _ condition right thenBranch elseBranch _, names =>
      let names := loopAccVars thenBranch (loopAccVars elseBranch names)
      loopInsert condition (match right with | .reg value => value :: names | .imm _ => names)
  | .arith operation, names =>
      match operation with
      | .longMul left right _ _ => loopInsertAll [left, right] names
      | .longDiv left right _ _ _ => loopInsertAll [left, right] names
      | .div destination _ _ => loopInsert destination names
  | .mark body, names => loopAccVars body names
  | .tick, names => names
  | .skip, names => names
  | .fail, names => names
  | .raise _, names => names
  | .return values, names => loopInsertAll values names
  | .call none _ arguments _, names => loopInsertAll arguments names
  | .call (some (returns, live)) _ arguments none, names =>
      loopInsertAll arguments (loopInsertAll returns (loopInsertAll live names))
  | .call (some (returns, live)) _ arguments
      (some (exception, handler, normal, handlerLive)), names =>
      let names := loopAccVars handler (loopAccVars normal names)
      loopInsertAll arguments
        (loopInsertAll returns (loopInsertAll live
          (loopInsert exception (loopInsertAll handlerLive names))))
  | .locValue destination source, names => loopInsert destination (loopInsert source names)
  | .assign destination expression, names =>
      loopInsertAll (loopVarsOfExp expression) (loopInsert destination names)
  | .primitive destinations _ arguments, names =>
      loopInsertAll arguments (loopInsertAll destinations names)
  | .shMem _ destination address, names =>
      loopInsertAll (loopVarsOfExp address) (loopInsert destination names)
  | .store address value, names =>
      loopInsertAll (loopVarsOfExp address) (loopInsert value names)
  | .setGlobal _ value, names => loopInsertAll (loopVarsOfExp value) names
  | .load32 address destination, names => loopInsert address (loopInsert destination names)
  | .loadByte address destination, names => loopInsert address (loopInsert destination names)
  | .store32 address value, names => loopInsertAll [address, value] names
  | .storeByte address value, names => loopInsertAll [address, value] names
  | .ffi _ configuration configurationLength array arrayLength live, names =>
      loopInsertAll [configuration, configurationLength, array, arrayLength]
        (loopInsertAll live names)

theorem loopVarsOfExp_load (address : LoopExp α) :
    loopVarsOfExp (.load address) = loopVarsOfExp address := by
  simp [loopVarsOfExp]

theorem loopAssignedVars_seq (first second : LoopProg α) :
    loopAssignedVars (.seq first second) =
      loopAssignedVars first ++ loopAssignedVars second := by
  simp [loopAssignedVars]

theorem loopAccVars_skip (names : List Nat) :
    loopAccVars (.skip : LoopProg α) names = names := by
  rfl

end Flapjack
