import Flapjack.LoopSemantics
import Flapjack.LoopSetVars

/-!
Faithful port of the original Pancake Loop `find_code`.

Source reference:
`cakeml/pancake/semantics/loopSemScript.sml:147-163`

```
(find_code (SOME p) args code =
   case sptree$lookup p code of
   | NONE => NONE
   | SOME (params,exp) => if LENGTH args = LENGTH params
                          then SOME (fromAList (ZIP (params, args)),exp) else NONE) /\
(find_code NONE args code =
   if args = [] then NONE else
     case LAST args of
     | Loc loc 0 =>
         (case lookup loc code of
          | NONE => NONE
          | SOME (params,exp) => if LENGTH args = LENGTH params + 1
                                 then SOME (fromAList (ZIP (params, FRONT args)),exp)
                                 else NONE)
     | other => NONE)
```

Normalizations matching the other Loop parity ports:

* the original `code : (num list # 'a loopLang$prog) num_map` is modeled as an
  association list (the same list `Flapjack.lookupLoopFunction` consumes);
* the original `'a word_loc` is modeled by `LoopWordLoc`, exposing exactly the
  `Word` and `Loc loc 0` shapes the definition inspects;
* `fromAList (ZIP (params, args))` is the first-occurrence-wins overlay
  `Flapjack.loopSetVars` (`Flapjack/LoopSetVars.lean`), which matches the
  original `ALOOKUP`/`alist_insert` behaviour validated by the HOL probe
  `scripts/hol-probes/loop_sem_find_code_probeScript.sml`.
-/

namespace Flapjack

/-- Mirror of the original `word_loc` shapes `find_code` inspects. -/
inductive LoopWordLoc where
  | word (value : Nat)
  | loc (identifier offset : Nat)
  deriving BEq, DecidableEq, Repr

/-- The code table is an association list of `(label, parameters, body)`. -/
abbrev LoopCode (α : Type u) := List (Nat × List Nat × LoopProg α)

/-- `find_code` from `loopSemScript.sml:147-163`. -/
def findLoopCode (label : Option Nat) (args : List LoopWordLoc)
    (code : LoopCode LoopWordLoc) :
    Option ((Nat → Option LoopWordLoc) × LoopProg LoopWordLoc) :=
  match label with
  | some entry =>
      match lookupLoopFunction entry code with
      | none => none
      | some (parameters, body) =>
          if args.length = parameters.length then
            some (loopSetVars (fun _ => none) parameters args, body)
          else none
  | none =>
      if args = [] then none
      else
        match args.getLast? with
        | some (.loc identifier 0) =>
            match lookupLoopFunction identifier code with
            | none => none
            | some (parameters, body) =>
                if args.length = parameters.length + 1 then
                  some (loopSetVars (fun _ => none) parameters args.dropLast,
                    body)
                else none
        | _ => none

theorem findLoopCode_none_empty (code : LoopCode LoopWordLoc) :
    findLoopCode none [] code = none :=
  rfl

theorem findLoopCode_entry_missing (entry : Nat) (args : List LoopWordLoc)
    (code : LoopCode LoopWordLoc)
    (missing : lookupLoopFunction entry code = none) :
    findLoopCode (some entry) args code = none := by
  simp [findLoopCode, missing]

end Flapjack
