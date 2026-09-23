(*
  Direct HOL observations for the crepSem$state.locals cell shape.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:21-31 (state field
  `locals : varname |-> 'a word_lab`), :55-57 (set_var_def) and :57-60
  (upd_locals_def).  Values written to locals keep the `word_lab` wrapper
  (`Word w`), and `eval` of a `Var` returns that wrapped cell unchanged.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;
val s0 = ``(^s with locals := FEMPTY)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "locals_set_var_cell"
  ``let s' = crepSem$set_var 3 (Word (7w:8 word)) ^s0 in
      FLOOKUP s'.locals 3``;

val _ = print_eval "locals_set_var_other_absent"
  ``let s' = crepSem$set_var 3 (Word (7w:8 word)) ^s0 in
      FLOOKUP s'.locals 9``;

val _ = print_eval "locals_eval_var"
  ``let s' = crepSem$set_var 3 (Word (7w:8 word)) ^s0 in
      crepSem$eval s' (crepLang$Var 3)``;

val _ = print_eval "locals_eval_var_missing"
  ``let s' = crepSem$set_var 3 (Word (7w:8 word)) ^s0 in
      crepSem$eval s' (crepLang$Var 9)``;

val _ = print_eval "locals_upd_locals_cells"
  ``let s' = crepSem$upd_locals
        [(2,(Word (5w:8 word))); (3,(Word (7w:8 word)))] ^s0 in
      (FLOOKUP s'.locals 2, FLOOKUP s'.locals 3)``;

val _ = print_eval "locals_set_var_overwrite"
  ``let s' = crepSem$set_var 3 (Word (7w:8 word)) ^s0 in
      let s'' = crepSem$set_var 3 (Word (9w:8 word)) s' in
      FLOOKUP s''.locals 3``;
