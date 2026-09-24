import Flapjack.Pancake.CrepLang
import Flapjack.Basis.Pure.MlString
import Flapjack.FiniteMap.Basic

/-!
The Loop intermediate language used after Crepe lowering. The constructors
follow CakeML's `loopLangScript.sml`; target-specific instruction selection is
kept for the later RISC-V layer.
-/

namespace Flapjack

inductive LoopExp (α : Type u) where
  | const (value : α)
  | var (name : Nat)
  | lookup (address : BitVec 5)
  | load (address : LoopExp α)
  | op (operator : BinOp) (args : List (LoopExp α))
  | crepOp (operator : CrepOp) (args : List (LoopExp α))
  | cmp (operator : Cmp) (left right : LoopExp α)
  | shift (operator : Shift) (left right : LoopExp α)
  | baseAddr
  | topAddr
  deriving Repr

/-- Faithful Cake `loopLang$exp` over a fixed word width. HOL's generic `'a word`
carrier is instantiated at `BitVec width`, and unlike the executable `LoopExp`
there are no extra `crepOp`/`cmp` cases. -/
@[hol "cakeml/pancake/loopLangScript.sml" "exp"]
inductive HolLoopExp (width : Nat) [NeZero width] where
  | const (value : BitVec width)
  | var (name : Nat)
  | lookup (address : BitVec 5)
  | load (address : HolLoopExp width)
  | op (operator : BinOp) (args : List (HolLoopExp width))
  | shift (operator : Shift) (left right : HolLoopExp width)
  | baseAddr
  | topAddr
  deriving Repr

/-- Executable `LoopExp` view of a faithful `HolLoopExp`. Every HOL constructor
has a direct executable counterpart; the executable language has additional
constructors that are not part of HOL `loopLang$exp`. -/
def holLoopExpToExecutable {width : Nat} [NeZero width] :
    HolLoopExp width → LoopExp (BitVec width)
  | .const value => .const value
  | .var name => .var name
  | .lookup address => .lookup address
  | .load address => .load (holLoopExpToExecutable address)
  | .op operator args => .op operator (args.map holLoopExpToExecutable)
  | .shift operator left right =>
      .shift operator (holLoopExpToExecutable left) (holLoopExpToExecutable right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr

inductive RegImm (α : Type u) where
  | imm (value : α)
  | reg (name : Nat)
  deriving Repr

/-- Faithful Cake `loopLang$loop_arith`; constructor and field shapes match this
executable `LoopArith` name for name (HOL uses `LLongMul`/`LLongDiv`/`LDiv`). -/
@[hol "cakeml/pancake/loopLangScript.sml" "loop_arith"]
inductive LoopArith where
  | longMul (destinationLeft destinationRight sourceLeft sourceRight : Nat)
  | longDiv (destinationLeft destinationRight sourceLeft sourceRight quotient : Nat)
  | div (destination dividend divisor : Nat)
  deriving Repr, DecidableEq

/-- **Untagged approximation** of Cake `loopLang$prog` over a fixed word width.
Not claimed as an exact HOL port: the `num_set` fields use `FiniteMap Nat Unit`,
whereas HOL `num_set` is `unit spt` (`miscScript.sml:787`); a finite map is an
unrestricted function and loses the `sptree` well-formedness/structure, so only
order-insensitive domain predicates bridge across (`docs/NUM-SET-AUDIT.md`), and
a datatype tag would over-claim. The exact `spt`-backed carrier is tracked by
bead `flapjack-pxn.18.5.17.1.1.1`. The other carriers here are faithful: word
width is fixed at `BitVec width`, `shMem` uses `CrepMemOp`, whose eight
constructors (`load/load8/load16/load32/store/store8/store16/store32`) match
`asm$memop` (`asmScript.sml:125-128`) name for name, and the FFI name is the
exact `MlString` carrier rather than the executable `FunName = String`. The
executable `LoopProg` is itself a one-parameter superset (`LoopExp` adds
`crepOp`/`cmp`; FFI names are `String`), so the executable/faithful bridge is
also tracked by bead `flapjack-pxn.18.5.17.1.1`. -/
inductive HolLoopProg (width : Nat) [NeZero width] where
  | skip
  | assign (name : Nat) (value : HolLoopExp width)
  | primitive (destinations : List Nat) (operator : PrimOp) (arguments : List Nat)
  | arith (operation : LoopArith)
  | store (address : HolLoopExp width) (value : Nat)
  | setGlobal (address : BitVec 5) (value : HolLoopExp width)
  | load32 (address destination : Nat)
  | loadByte (address destination : Nat)
  | store32 (address value : Nat)
  | storeByte (address value : Nat)
  | seq (first second : HolLoopProg width)
  | ite (operator : Cmp) (condition : Nat) (right : RegImm (BitVec width))
      (thenBranch elseBranch : HolLoopProg width) (live : FiniteMap Nat Unit)
  | loop (liveIn : FiniteMap Nat Unit) (body : HolLoopProg width) (liveOut : FiniteMap Nat Unit)
  | break (label : Nat)
  | continue (label : Nat)
  | raise (exception : Nat)
  | return (values : List Nat)
  | shMem (operator : CrepMemOp) (name : Nat) (address : HolLoopExp width)
  | tick
  | mark (body : HolLoopProg width)
  | fail
  | locValue (destination source : Nat)
  | call (returns : Option (List Nat × FiniteMap Nat Unit)) (target : Option Nat)
      (arguments : List Nat)
      (handler : Option (Nat × HolLoopProg width × HolLoopProg width × FiniteMap Nat Unit))
  | ffi (function : Flapjack.Basis.Pure.MlString.MlString)
      (configuration configurationLength array arrayLength : Nat)
      (live : FiniteMap Nat Unit)

inductive LoopProg (α : Type u) where
  | skip
  | assign (name : Nat) (value : LoopExp α)
  | primitive (destinations : List Nat) (operator : PrimOp) (arguments : List Nat)
  | arith (operation : LoopArith)
  | store (address : LoopExp α) (value : Nat)
  | setGlobal (address : BitVec 5) (value : LoopExp α)
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

/-! Faithful port of Cake `loop_seqs_def` from
    `cakeml/pancake/pan_passesScript.sml:532`: flatten only `Seq` nodes,
    preserving the left-to-right order of every other Loop statement. -/
def loopSeqs : LoopProg α → List (LoopProg α)
  | .seq first second => loopSeqs first ++ loopSeqs second
  | program => [program]
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

end Flapjack
