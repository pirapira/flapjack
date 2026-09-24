(* Direct HOL observations for the carriers of `crep_to_loopProofScript.sml`
   `locals_rel_def` (lines 101-111):
     locals_rel ctxt (l:sptree$num_set) (s_locals:num |-> 'a word_lab) t_locals
   The relation is a universally quantified Prop, so the rows below evaluate its
   atomic pointwise obligations at a concrete context finite map, a concrete
   `num_set` (membership is extensionally `lookup n l = SOME ()`) and a concrete
   `num_map`. *)
load "bossLib";
load "preamble";
load "mlstringTheory";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open mlstringTheory;
open crep_to_loopProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

(* ctxt.vars : mlstring |-> num, with «x» |-> 2 and «y» |-> 4. *)
val vars = ``((FEMPTY |+ («x», (2:num)) |+ («y», (4:num)))
               : (mlstring, num) fmap)``;
(* l : num_set with members 1 and 2; t : num_map with both present. *)
val l = ``(sptree$fromAList [(1:num,());(2:num,())] : sptree$num_set)``;
val t = ``(sptree$fromAList
             [(1:num, Word (7w:8 word)); (2:num, Word (9w:8 word))]
             : 8 word_loc sptree$num_map)``;

val _ = print_eval "ctxt_vars_lookup" (``FLOOKUP ^vars «x» = SOME 2``);
val _ = print_eval "distinct_component"
  (``case (FLOOKUP ^vars «x», FLOOKUP ^vars «y») of
      | (SOME a, SOME b) => (a = b ==> («x» = «y»))
      | _ => T``);
val _ = print_eval "ctxt_max_component"
  (``case FLOOKUP ^vars «y» of SOME m => m <= 5 | NONE => T``);
val _ = print_eval "set_domain_mem"
  (``sptree$lookup (2:num) ^l = SOME ()``);
val _ = print_eval "map_lookup"
  (``sptree$lookup (2:num) ^t = SOME (Word (9w:8 word))``);
val _ = print_eval "subset_domain_component"
  (``sptree$lookup (2:num) ^l = SOME () ==>
      sptree$lookup (2:num) ^t <> NONE``);