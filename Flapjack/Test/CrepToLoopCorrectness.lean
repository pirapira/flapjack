import Flapjack.CrepToLoopCorrectness

/-!
Focused Cake-backed guards for the context lookup boundary.  The old file
contained identity-map evaluation witnesses; those are not valid after the
Crep compiler began applying `find_var` to source slots.
-/

namespace Flapjack

def crepLookupContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

#guard crepFindVar crepLookupContext 1 = 5
#guard crepFindVar crepLookupContext 2 = 0

end Flapjack
