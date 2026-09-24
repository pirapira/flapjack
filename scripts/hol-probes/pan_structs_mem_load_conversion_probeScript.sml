(* Direct HOL checks for One/Comb/nested-Named cases of
   pan_structsProof$mem_load_conversion. *)
load "bossLib";
load "preamble";
load "pan_structsTheory";
load "pan_structsProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory pan_structsTheory pan_structsProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

fun print_conversion label th =
  (print (label ^ "=");
   print_term (rconc th);
   print "\n")

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

val named_struct_ctxt =
  ``[(strlit "Pair", <| fields := [(strlit "inner", Named (strlit "Inner"));
                                   (strlit "last", One)]; size := 3 |>);
     (strlit "Inner", <| fields := [(strlit "left", One);
                                     (strlit "right", One)]; size := 2 |>)]``;
val named_shape_ctxt =
  ``MAP (λ(nm,info). (nm,info.fields)) ^named_struct_ctxt``;
val named_shape = ``Named (strlit "Pair")``;
val named_domain = ``{0w:8 word; 1w; 2w}``;
val named_memory =
  ``\a:8 word. if a = 0w then Word (7w:8 word)
      else if a = 1w then Word (11w:8 word)
      else if a = 2w then Word (13w:8 word)
      else ARB``;
val named_value =
  ``NStruct (strlit "Pair")
      [(strlit "inner", NStruct (strlit "Inner")
        [(strlit "left", ValWord (7w:8 word));
         (strlit "right", ValWord (11w:8 word))]);
       (strlit "last", ValWord (13w:8 word))]``;

(* EVAL leaves the bounded universal in struct_infos_ok_def open even for this
   concrete two-entry context. Prove the HOL antecedent from the source
   struct_infos_ok_cons theorem, then rewrite that proved Bool result to T in
   the printed oracle row. *)
val named_struct_infos_ok = prove
  (``struct_infos_ok ^named_struct_ctxt``,
   SIMP_TAC (srw_ss()) [struct_infos_ok_cons, struct_infos_ok_def,
     is_wf_shape_def, size_of_sh_with_ctxt_def]);

val _ = print_conversion "mem_load_conversion_named_nested_struct_infos_ok"
  (REWRITE_CONV [EQT_INTRO named_struct_infos_ok]
    ``struct_infos_ok ^named_struct_ctxt``);

val named_source_load =
  ``mem_load ^named_shape 0w ^named_domain ^named_memory ^named_struct_ctxt``;
val named_compiled_load =
  ``mem_load (compile_shape_n ^named_shape_ctxt 0 ^named_shape) 0w
      ^named_domain ^named_memory ^named_struct_ctxt``;
val _ = print_eval "mem_load_conversion_named_nested"
  ``(is_wf_shape (DROP 0 ^named_struct_ctxt) ^named_shape,
     ^named_source_load,
     ^named_compiled_load,
     ^named_source_load = SOME ^named_value,
     ^named_compiled_load = SOME (convert_v ^named_value),
     v_flds_ok ^named_struct_ctxt ^named_value,
     size_of_sh_with_ctxt []
       (compile_shape_n ^named_shape_ctxt 0 ^named_shape) =
       size_of_sh_with_ctxt ^named_struct_ctxt ^named_shape)
     ``;
