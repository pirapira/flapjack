import Flapjack.RiscV.CorrectnessStackParallelMove

/-!
# StackLang function-entry composition

The function-entry lowering is a physical move prefix followed by a lowered
Word body.  These equations expose the sequencing boundary needed by the
spill-aware function simulation, while retaining the abstract
Word-to-Stack machine state.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_wordStackJoin [NeZero width]
    (state middle final : WordStackMachineState width)
    (first second : StackProg Nat)
    (hfirst : evalWordStackMachine state first = some middle)
    (hsecond : evalWordStackMachine middle second = some final) :
    evalWordStackMachine state (wordStackJoin first second) = some final := by
  by_cases hfirstSkip : first = .skip
  · subst first
    simp [wordStackJoin, evalWordStackMachine] at hfirst ⊢
    cases hfirst
    exact hsecond
  by_cases hsecondSkip : second = .skip
  · subst second
    have hmiddle : middle = final := by
      simpa [evalWordStackMachine] using hsecond
    subst final
    simpa [wordStackJoin] using hfirst
  · rw [wordStackJoin_eq_seq_of_ne_skip first second hfirstSkip hsecondSkip]
    simp [evalWordStackMachine, hfirst, hsecond]

theorem evalWordStackMachine_wordToStackFunctionWithParameters
    [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width))
    (body moves : StackProg Nat)
    (state middle final : WordStackMachineState width)
    (hbody :
      wordToStackProgWord config program = some body)
    (hmoves :
      wordStackMovesFromPhysical config parameters 2 = some moves)
    (hentry : evalWordStackMachine state moves = some middle)
    (hbodyEval : evalWordStackMachine middle body = some final) :
    evalWordStackMachine state
      ((wordToStackFunctionWithParameters config parameters program).getD .skip) =
      some final := by
  simpa [wordToStackFunctionWithParameters, hbody, hmoves] using
    (evalWordStackMachine_wordStackJoin state middle final moves body
      hentry hbodyEval)

end Flapjack.RiscV
