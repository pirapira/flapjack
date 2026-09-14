import Flapjack.Compile
import Flapjack.RiscV.Model

/-!
Executable arithmetic simplification for Crepe.

CakeML's `crep_arith` pass folds constant `Mul` nodes before the
Crepe-to-Loop boundary.  Keeping this pass separate makes its placement in
the pipeline explicit and leaves the transformation available to clients
that inspect intermediate artifacts.
-/

namespace Flapjack

def crepDestConst : CrepExp α → Option α
  | .const value => some value
  | _ => none

/-! Fixed-width executable port of CakeML's `crep_arith$dest_2exp`
    (`cakeml/pancake/crep_arithScript.sml:15`).  The HOL definition recurses
    while stripping low zero bits from a nonzero word.  A width-plus-one fuel
    bound is sufficient for a `BitVec`: every unsuccessful recursive step
    shifts away one bit, and the next value is either zero, one, or odd. -/
def crepDest2ExpAux [NeZero width] : Nat → Nat → RiscV.Word width → Option Nat
  | 0, _, _ => none
  | fuel + 1, exponent, word =>
      if word == 0 then none
      else if word == 1 then some exponent
      else if (word &&& BitVec.ofNat width 1) != 0 then none
      else crepDest2ExpAux fuel (exponent + 1) (word >>> 1)

def crepDest2Exp [NeZero width] (word : RiscV.Word width) : Option Nat :=
  crepDest2ExpAux (width + 1) 0 word

/-! Fixed-width executable port of CakeML's `crep_arith$mul_const`.
    Constants zero and one are handled directly; powers of two become a left
    shift, while all other constants retain the original multiplication node. -/
def crepMulConst [NeZero width]
    (expression : CrepExp (RiscV.Word width))
    (constant : RiscV.Word width) : CrepExp (RiscV.Word width) :=
  if constant == 0 then .const 0
  else if constant == 1 then expression
  else match crepDest2Exp constant with
    | none => .crepOp .mul [expression, .const constant]
    | some exponent => .shift .lsl expression
        (.const (BitVec.ofNat width exponent))

/-! Fixed-width executable port of CakeML's `crep_arith$simp_exp`.
    The expression tree is simplified bottom-up.  Only binary multiplication
    receives arithmetic-specific treatment; all other constructors preserve
    their original shape after recursively simplifying their children. -/
def crepSimpExp [NeZero width] : CrepExp (RiscV.Word width) →
    CrepExp (RiscV.Word width)
  | .load address => .load (crepSimpExp address)
  | .load32 address => .load32 (crepSimpExp address)
  | .loadByte address => .loadByte (crepSimpExp address)
  | .op operator expressions => .op operator (expressions.map crepSimpExp)
  | .crepOp operator expressions =>
      let expressions := expressions.map crepSimpExp
      match operator, expressions with
      | .mul, [.const left, .const right] => .const (left * right)
      | .mul, [.const constant, expression] =>
          crepMulConst expression constant
      | .mul, [expression, .const constant] =>
          crepMulConst expression constant
      | _, _ => .crepOp operator expressions
  | .cmp operator left right =>
      .cmp operator (crepSimpExp left) (crepSimpExp right)
  | .shift operator left right =>
      .shift operator (crepSimpExp left) (crepSimpExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

def crepArithExp [Mul α] : CrepExp α → CrepExp α
  | .load address => .load (crepArithExp address)
  | .load32 address => .load32 (crepArithExp address)
  | .loadByte address => .loadByte (crepArithExp address)
  | .op operator expressions => .op operator (expressions.map crepArithExp)
  | .crepOp operator expressions =>
      let expressions := expressions.map crepArithExp
      match operator, expressions with
      | .mul, [.const left, .const right] => .const (left * right)
      | _, _ => .crepOp operator expressions
  | .cmp operator left right =>
      .cmp operator (crepArithExp left) (crepArithExp right)
  | .shift operator left right =>
      .shift operator (crepArithExp left) (crepArithExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

def crepArithProg [Mul α] : CrepProg α → CrepProg α
  | .skip => .skip
  | .dec name value body =>
      .dec name (crepArithExp value) (crepArithProg body)
  | .assign name value => .assign name (crepArithExp value)
  | .primitive names operator arguments =>
      .primitive names operator arguments
  | .store address value =>
      .store (crepArithExp address) (crepArithExp value)
  | .store32 address value =>
      .store32 (crepArithExp address) (crepArithExp value)
  | .storeByte address value =>
      .storeByte (crepArithExp address) (crepArithExp value)
  | .storeGlob address value =>
      .storeGlob address (crepArithExp value)
  | .seq first second =>
      .seq (crepArithProg first) (crepArithProg second)
  | .ite condition thenBranch elseBranch =>
      .ite (crepArithExp condition) (crepArithProg thenBranch)
        (crepArithProg elseBranch)
  | .while condition body =>
      .while (crepArithExp condition) (crepArithProg body)
  | .break label => .break label
  | .continue label => .continue label
  | .call none name arguments =>
      .call none name (arguments.map crepArithExp)
  | .call (some (names, none)) name arguments =>
      .call (some (names, none)) name (arguments.map crepArithExp)
  | .call (some (names, some (handler, body))) name arguments =>
      .call (some (names, some (handler, crepArithProg body))) name
        (arguments.map crepArithExp)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function configuration configurationLength array arrayLength
  | .raise exception => .raise exception
  | .return values => .return (values.map crepArithExp)
  | .shMem operator name address =>
      .shMem operator name (crepArithExp address)
  | .tick => .tick
termination_by program => sizeOf program
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

def crepArithFunctions [Mul α] : List (CompiledFunction α) →
    List (CompiledFunction α)
  | [] => []
  | function :: functions =>
      { function with body := crepArithProg function.body } ::
        crepArithFunctions functions

end Flapjack
