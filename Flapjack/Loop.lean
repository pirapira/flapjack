import Flapjack.Crepe

/-!
The Loop intermediate language used after Crepe lowering. The constructors
follow CakeML's `loopLangScript.sml`; target-specific instruction selection is
kept for the later RISC-V layer.
-/

namespace Flapjack

inductive LoopExp (α : Type u) where
  | const (value : α)
  | var (name : Nat)
  | lookup (address : α)
  | load (address : LoopExp α)
  | op (operator : BinOp) (args : List (LoopExp α))
  | crepOp (operator : CrepOp) (args : List (LoopExp α))
  | cmp (operator : Cmp) (left right : LoopExp α)
  | shift (operator : Shift) (left right : LoopExp α)
  | baseAddr
  | topAddr
  deriving Repr

inductive RegImm (α : Type u) where
  | imm (value : α)
  | reg (name : Nat)
  deriving Repr

inductive LoopArith where
  | longMul (destinationLeft destinationRight sourceLeft sourceRight : Nat)
  | longDiv (destinationLeft destinationRight sourceLeft sourceRight quotient : Nat)
  | div (destination dividend divisor : Nat)
  deriving Repr

inductive LoopProg (α : Type u) where
  | skip
  | assign (name : Nat) (value : LoopExp α)
  | primitive (destinations : List Nat) (operator : PrimOp) (arguments : List Nat)
  | arith (operation : LoopArith)
  | store (address : LoopExp α) (value : Nat)
  | setGlobal (address : α) (value : LoopExp α)
  | load32 (address destination : Nat)
  | loadByte (address destination : Nat)
  | store32 (address value : Nat)
  | storeByte (address value : Nat)
  | seq (first second : LoopProg α)
  | ite (operator : Cmp) (condition : Nat) (right : RegImm α)
      (thenBranch elseBranch : LoopProg α) (live : List Nat)
  | loop (liveIn : List Nat) (body : LoopProg α) (liveOut : List Nat)
  | break (label : Nat)
  | continue (label : Nat)
  | raise (exception : Nat)
  | return (values : List Nat)
  | shMem (operator : CrepMemOp) (name : Nat) (address : LoopExp α)
  | tick
  | mark (body : LoopProg α)
  | fail
  | locValue (destination source : Nat)
  | call (returns : Option (List Nat × List Nat)) (target : Option Nat)
      (arguments : List Nat)
      (handler : Option (Nat × LoopProg α × LoopProg α × List Nat))
  | ffi (function : FunName) (configuration configurationLength array arrayLength : Nat)
      (live : List Nat)
  deriving Repr

def loopNestedSeq : List (LoopProg α) → LoopProg α
  | [] => .skip
  | statement :: statements => .seq statement (loopNestedSeq statements)

end Flapjack
