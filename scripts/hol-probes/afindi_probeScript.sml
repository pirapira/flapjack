(* Direct HOL-EVAL fixture for pan_structs$afindi_def. *)
load "bossLib";
load "preamble";
load "pan_structsProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_structsProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "empty"
  ``pan_structs$afindi «a» []``;
val _ = print_eval "first"
  ``pan_structs$afindi «a» [(«a», 10); («b», 20)]``;
val _ = print_eval "middle"
  ``pan_structs$afindi «b» [(«a», 10); («b», 20); («c», 30)]``;
val _ = print_eval "last"
  ``pan_structs$afindi «c» [(«a», 10); («b», 20); («c», 30)]``;
val _ = print_eval "missing"
  ``pan_structs$afindi «z» [(«a», 10); («b», 20); («c», 30)]``;
val _ = print_eval "duplicate_first"
  ``pan_structs$afindi «a» [(«a», 10); («b», 20); («a», 30)]``;
val wf_drop_context =
  ``[(«prefix», []); («s», [(«field», panLang$One)])]``;
val _ = print_eval "wf_shape_drop"
  ``panLang$is_wf_shape (DROP 1 ^wf_drop_context) (panLang$Named «s») ==>
    panLang$is_wf_shape ^wf_drop_context (panLang$Named «s»)``;
val dropwhile_source = ``[0; 1; 2; 3]``;
val _ = print_eval "dropWhile_MAP_helper"
  ``dropWhile (\n:num. n < 3) (MAP SUC ^dropwhile_source) =
    MAP SUC (dropWhile (\n:num. n < 2) ^dropwhile_source)``;
val _ = print_eval "UNCURRY_EQ_o_SND_pair"
  ``UNCURRY (\x. SUC) (0, 4) = SUC 4``;
val _ = print_eval "map_uncurry_zip_again"
  ``MAP (\(x, y). (SUC x, SUC y)) (ZIP ([1; 2], [3; 4])) =
    ZIP (MAP SUC [1; 2], MAP SUC [3; 4])``;
val valid_struct_context =
  ``[(strlit "S", <| fields := [(strlit "f", One)]; size := 1 |>)]``;
val struct_infos_ok_drop_instance =
  INST [{redex = mk_var ("sh_ctxt", type_of valid_struct_context),
         residue = valid_struct_context},
        {redex = mk_var ("n", type_of ``1``), residue = ``1``}]
    struct_infos_ok_drop;
val _ = print "struct_infos_ok_drop=";
val _ = print
  (String.translate (fn #"\n" => " " | c => String.str c)
    (term_to_string (concl struct_infos_ok_drop_instance)));
val _ = print "\n";
val empty_struct_context = mk_const ("NIL", type_of valid_struct_context);
val struct_infos_ok_append_instance =
  INST [{redex = mk_var ("xs", type_of valid_struct_context),
         residue = empty_struct_context},
        {redex = mk_var ("ys", type_of valid_struct_context),
         residue = valid_struct_context}]
    struct_infos_ok_append;
val _ = print "struct_infos_ok_append=";
val _ = print
  (String.translate (fn #"\n" => " " | c => String.str c)
    (term_to_string (concl struct_infos_ok_append_instance)));
val _ = print "\n";
