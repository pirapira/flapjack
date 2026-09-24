(* Direct HOL observations for `crep_to_loopScript.sml` `find_var_def`
   (lines 20-25) and `find_lab_def` (lines 27-32):
     find_var ct v = case FLOOKUP ct.vars v of SOME n => n | NONE => 0
     find_lab ct f = case FLOOKUP ct.funcs f of SOME (n,_) => n | NONE => 0
   `context.vars` is `crepLang$varname |-> num` (= num keys) and
   `.funcs` is `crepLang$funname |-> num # num` (= mlstring keys); the Lean
   carrier `CrepToLoopFiniteMapContext` uses the same key types. *)
load "bossLib";
load "preamble";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val ct = (``context ((FEMPTY |+ ((1:num), (7:num))) : (num, num) fmap)
                                 ((FEMPTY |+ ((«f»:mlstring), ((3:num), (2:num)))) :
                                    (mlstring, num # num) fmap)
                                 (9:num) ARMv7``);

val _ = print_eval "find_var_hit" ``find_var ^ct (1:num) = 7``;
val _ = print_eval "find_var_miss" ``find_var ^ct (2:num) = 0``;
val _ = print_eval "find_lab_hit" ``find_lab ^ct («f»:mlstring) = 3``;
val _ = print_eval "find_lab_miss" ``find_lab ^ct («g»:mlstring) = 0``;