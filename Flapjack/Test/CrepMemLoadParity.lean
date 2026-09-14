import Flapjack.CrepMemLoad
import Flapjack.Test.CrepeSemantics

/-!
# Parity checks for `crepSem$mem_load_def`

The direct HOL fixture records a hit and a domain miss.  The Lean checks use
the same two cases and verify that a hit reads the source memory while a miss
does not expose an out-of-domain cell.
-/

namespace Flapjack.Test.CrepMemLoadParity

open Flapjack

def hit : Bool :=
  crepSemMemLoad
      { crepeRuntimeState with
        memory := fun address => if address == 3 then some 7 else none
        memaddrs := fun address => address == 3 }
      3 == some 7

def miss : Bool :=
  crepSemMemLoad
      { crepeRuntimeState with
        memory := fun address => if address == 3 then some 7 else none
        memaddrs := fun address => address == 3 }
      4 == none

#guard hit
#guard miss

def runChecks : IO Bool := do
  if hit then IO.println "PASS crep mem_load reads an in-domain address"
  else IO.println "FAIL crep mem_load reads an in-domain address"
  if miss then IO.println "PASS crep mem_load rejects an out-of-domain address"
  else IO.println "FAIL crep mem_load rejects an out-of-domain address"
  pure (hit && miss)

end Flapjack.Test.CrepMemLoadParity
