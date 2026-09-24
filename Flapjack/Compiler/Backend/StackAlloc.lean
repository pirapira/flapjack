import Flapjack.Compiler.Backend.StackLang

/-!
# Faithful StackAlloc support definitions

The `nextLab` equation ports `stack_allocScript.sml:649-662` over the generic
HOL Stack AST. The existing `Flapjack.StackAlloc.stackAllocNextLab` remains the
executable Flapjack-`StackProg` implementation; no correspondence is asserted
between the two ASTs here.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open StackLang

/-- HOL `stack_alloc$next_lab`, including its traversal order and label seed. -/
def nextLab {Inst Cmp RegImm Binop Memop Addr MlString : Type} :
    Flapjack.Compiler.Backend.StackLang.Prog Inst Cmp RegImm Binop Memop Addr MlString → Nat → Nat
  | .seq first second, next => nextLab first (nextLab second next)
  | .ite _ _ _ thenBranch elseBranch, next =>
      nextLab thenBranch (nextLab elseBranch next)
  | .loop body, next => nextLab body next
  | .call none _ none, next => next
  | .call none _ (some (_, _, handlerLabel)), next =>
      max next (handlerLabel + 2)
  | .call (some (returnProgram, _, _, returnLabel)) _ none, next =>
      nextLab returnProgram (max next (returnLabel + 2))
  | .call (some (returnProgram, _, _, returnLabel)) _
      (some (handlerProgram, _, handlerLabel)), next =>
      nextLab returnProgram
        (nextLab handlerProgram (max (max returnLabel handlerLabel + 2) next))
  | _, next => next
termination_by program _next => sizeOf program
decreasing_by all_goals decreasing_trivial

end Flapjack.Compiler.Backend.StackAlloc
