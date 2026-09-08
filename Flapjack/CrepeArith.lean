import Flapjack.Compile

/-!
Executable arithmetic simplification for Crepe.

CakeML's `crep_arith` pass folds constant `Mul` nodes before the
Crepe-to-Loop boundary.  Keeping this pass separate makes its placement in
the pipeline explicit and leaves the transformation available to clients
that inspect intermediate artifacts.
-/

namespace Flapjack

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
