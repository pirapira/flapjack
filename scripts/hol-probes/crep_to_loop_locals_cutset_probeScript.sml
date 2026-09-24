(* Direct HOL observations for the carriers of `crep_to_loopProofScript.sml`
   `locals_rel_cutset_prop` (lines 239-249):
     locals_rel ct cset lcl lcl' /\ locals_rel ct cset' lcl lcl'' /\
     subspt cset cset' ==> locals_rel ct cset lcl lcl''
   The relation and `subspt` are universally quantified Props, so the rows
   below evaluate their atomic pointwise obligations at concrete `num_set`s
   (membership is extensionally `sptree$lookup n s = SOME ()`) and a concrete
   `num_map`: the cut-set is a sub-map (`cset` keys also live in `cset'`), and
   the target lookups survive. *)
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

(* cset : num_set with members 0 and 1; cset' : larger num_set with 0,1,2. *)
val cset = ``(sptree$fromAList [(0:num,());(1:num,())] : sptree$num_set)``;
val cset' = ``(sptree$fromAList [(0:num,());(1:num,());(2:num,())]
                : sptree$num_set)``;
(* lcl'' : num_map with both cut-set keys present. *)
val lcl'' = ``(sptree$fromAList
                 [(0:num, Word (9w:8 word)); (2:num, Word (7w:8 word))]
                 : 8 word_loc sptree$num_map)``;

val _ = print_eval "cutset_sub_0"
  (``sptree$lookup (0:num) ^cset' = SOME ()``);
val _ = print_eval "cutset_sub_1"
  (``sptree$lookup (1:num) ^cset' = SOME ()``);
val _ = print_eval "cutset_sub_absent"
  (``sptree$lookup (9:num) ^cset' = NONE``);
val _ = print_eval "cutset_lookup_preserved"
  (``sptree$lookup (0:num) ^lcl'' = SOME (Word (9w:8 word))``);
val _ = print_eval "cutset_lookup_other"
  (``sptree$lookup (2:num) ^lcl'' = SOME (Word (7w:8 word))``);
val _ = print_eval "cutset_domain_trans"
  (``sptree$lookup (0:num) ^cset = SOME () ==>
      sptree$lookup (0:num) ^lcl'' <> NONE``);