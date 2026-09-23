(* Direct HOL-EVAL cases for the One/Comb branches of
   pan_structsProof$mem_load_conversion. *)
load "bossLib";
load "preamble";
load "pan_structsTheory";
load "pan_structsProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val scalar_domain = ``{0w:8 word}``;
val scalar_memory = ``\a:8 word. if a = 0w then Word (7w:8 word) else ARB``;
val scalar_value = ``ValWord (7w:8 word)``;
val _ = print_eval "mem_load_conversion_one"
  ``(is_wf_shape [] One,
     struct_infos_ok [],
     mem_load One 0w ^scalar_domain ^scalar_memory [] = SOME ^scalar_value,
     mem_load (compile_shape [] One) 0w ^scalar_domain ^scalar_memory [] =
       SOME (convert_v ^scalar_value))``;

val comb_shape = ``Comb [One; Comb [One; One]]``;
val comb_domain = ``{0w:8 word; 1w; 2w}``;
val comb_memory =
  ``\a:8 word. if a = 0w then Word (7w:8 word)
      else if a = 1w then Word (11w:8 word)
      else if a = 2w then Word (13w:8 word)
      else ARB``;
val comb_value =
  ``RStruct [ValWord (7w:8 word);
             RStruct [ValWord (11w:8 word); ValWord (13w:8 word)]]``;
val _ = print_eval "mem_load_conversion_comb_multiword"
  ``(is_wf_shape [] ^comb_shape,
     struct_infos_ok [],
     mem_load ^comb_shape 0w ^comb_domain ^comb_memory [] = SOME ^comb_value,
     mem_load (compile_shape [] ^comb_shape) 0w ^comb_domain ^comb_memory [] =
       SOME (convert_v ^comb_value),
     size_of_sh_with_ctxt [] (compile_shape [] ^comb_shape) =
       size_of_sh_with_ctxt [] ^comb_shape)``;
