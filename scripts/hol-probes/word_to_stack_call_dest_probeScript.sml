(* Probe: exact HOL word_to_stack call_dest plus backend_common/wordLang stub
   constants.

   Bead flapjack-pxn.18.5.15.3.20.  Source:
   cakeml/compiler/backend/word_to_stackScript.sml call_dest_def (:264),
   cakeml/compiler/backend/wordLangScript.sml raise_stub_location_def (:70)
   and store_consts_stub_location_def (:73),
   cakeml/compiler/backend/backend_commonScript.sml stack_num_stubs_def (:124)
   and word_num_stubs_def (:128).

   Oracle provenance: read-only prebuilt checkout /home/zksecurity/flapjack2/cakeml,
   cakeml submodule HEAD 857f0d98da8f8a3580f2333897e0e, word_to_stackScript.sml
   sha256 prefix 3b487de8259affbf.
*)
load "bossLib";
load "preamble";
load "backend_commonTheory";
load "wordLangTheory";
load "word_to_stackTheory";
open bossLib HolKernel Parse preamble backend_commonTheory wordLangTheory word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val cd_some = ``((call_dest (SOME 3) [1;2] (2,7,9)
                 = (Skip, (INL 3 : (num, num) sum))) : bool)``;
val cd_none_reg = ``((call_dest NONE [1;2] (2,7,9)
                 = (Skip, (INR 1 : (num, num) sum))) : bool)``;
val cd_none_stack = ``((call_dest NONE [1;8] (2,7,9)
                 = (Seq (StackLoad 3 4) Skip, (INR 3 : (num, num) sum))) : bool)``;
val cd_empty = ``((call_dest NONE [] (2,7,9)
                 = (Skip, (INL (wordLang$raise_stub_location) : (num, num) sum))) : bool)``;
val bc_stack = ``((backend_common$stack_num_stubs = 5) : bool)``;
val bc_word = ``((backend_common$word_num_stubs = 7) : bool)``;
val wl_raise = ``((wordLang$raise_stub_location = 5) : bool)``;
val wl_store = ``((wordLang$store_consts_stub_location = 6) : bool)``;

val () = print_eval "cd_some" cd_some;
val () = print_eval "cd_none_reg" cd_none_reg;
val () = print_eval "cd_none_stack" cd_none_stack;
val () = print_eval "cd_empty" cd_empty;
val () = print_eval "bc_stack" bc_stack;
val () = print_eval "bc_word" bc_word;
val () = print_eval "wl_raise" wl_raise;
val () = print_eval "wl_store" wl_store;
