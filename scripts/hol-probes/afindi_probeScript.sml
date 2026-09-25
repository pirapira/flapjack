(* Direct HOL-EVAL fixture for pan_structs$afindi_def. *)
load "bossLib";
load "preamble";
load "pan_commonPropsTheory";
load "pan_structsProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_commonPropsTheory;
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
val cons_struct_name = ``strlit "S"``;
val cons_struct_info = ``<| fields := [(strlit "f", One)]; size := 1 |>``;
val struct_infos_ok_cons_instance =
  INST [{redex = mk_var ("xs", type_of valid_struct_context),
         residue = empty_struct_context},
        {redex = mk_var ("nm", type_of cons_struct_name),
         residue = cons_struct_name},
        {redex = mk_var ("info", type_of cons_struct_info),
         residue = cons_struct_info}]
    struct_infos_ok_cons;
val _ = print "struct_infos_ok_cons=";
val _ = print
  (String.translate (fn #"\n" => " " | c => String.str c)
    (term_to_string (concl struct_infos_ok_cons_instance)));
val _ = print "\n";
val alookup_map_structs_ok_oracle = prove(
  ``!s_ctxt nm info. ALOOKUP s_ctxt nm = SOME info /\
      struct_infos_ok s_ctxt ==> ALL_DISTINCT (MAP FST info.fields)``,
  rw [] >>
  imp_res_tac ALOOKUP_MEM >>
  fs [struct_infos_ok_def, EVERY_MAP] >>
  imp_res_tac EVERY_MEM >>
  fs []);
val alookup_map_context = valid_struct_context;
val alookup_map_name = ``strlit "S"``;
val alookup_map_info = ``<| fields := [(strlit "f", One)]; size := 1 |>``;
val alookup_map_structs_ok_instance =
  SPECL [alookup_map_context, alookup_map_name, alookup_map_info]
    alookup_map_structs_ok_oracle;
val _ = print "alookup_map_structs_ok=";
val _ = print
  (String.translate (fn #"\n" => " " | c => String.str c)
    (term_to_string (concl alookup_map_structs_ok_instance)));
val _ = print "\n";
val _ = print "fields_in_order_reorder_noop=";
val _ = print
  (String.translate (fn #"\n" => " " | c => String.str c)
    (term_to_string (concl fields_in_order_reorder_noop)));
val _ = print "\n";
val opt_mmap_eq_every_oracle = prove(
  ``!f xs ys P. OPT_MMAP f xs = SOME ys /\
      (!x y. MEM x xs /\ f x = SOME y ==> P y) ==> EVERY P ys``,
  rw [EVERY_EL] >>
  imp_res_tac opt_mmap_length_eq >> fs [] >>
  imp_res_tac opt_mmap_el >> fs [] >>
  gs [] >> res_tac >>
  metis_tac [EL_MEM]);
val _ = print "opt_mmap_eq_every=";
val _ = print
  (String.translate (fn #"\n" => " " | c => String.str c)
    (term_to_string (concl opt_mmap_eq_every_oracle)));
val _ = print "\n";
val _ = print_eval "alookup_drop_helper"
  ``ALOOKUP (DROP 1 [(strlit "a", 10); (strlit "b", 20)]) (strlit "b") = SOME 20 /\
    ALL_DISTINCT (MAP FST [(strlit "a", 10); (strlit "b", 20)]) ==>
    ~MEM (strlit "b") (MAP FST (TAKE 1 [(strlit "a", 10); (strlit "b", 20)])) /\
    ALOOKUP [(strlit "a", 10); (strlit "b", 20)] (strlit "b") = SOME 20``;
(* The HOL existential has the concrete witness i = 1 in this oracle row. *)
val _ = print_eval "map_fst_eq_alookup"
  ``MAP FST [(strlit "a", 1); (strlit "b", 2)] =
      MAP FST [(strlit "a", 3); (strlit "b", 4)] /\
    ALOOKUP [(strlit "a", 1); (strlit "b", 2)] (strlit "b") = SOME 2 ==>
    pan_structs$afindi (strlit "b") [(strlit "a", 1); (strlit "b", 2)] = SOME 1 /\
      pan_structs$afindi (strlit "b") [(strlit "a", 3); (strlit "b", 4)] = SOME 1 /\
      1 < LENGTH [(strlit "a", 1); (strlit "b", 2)] /\
      1 < LENGTH [(strlit "a", 3); (strlit "b", 4)] /\
      2 = SND (EL 1 [(strlit "a", 1); (strlit "b", 2)]) /\
      ALOOKUP [(strlit "a", 3); (strlit "b", 4)] (strlit "b") =
        SOME (SND (EL 1 [(strlit "a", 3); (strlit "b", 4)]))``;
(* HOL's key and value types are inferred independently by the source
   statement. This instance uses Nat values in xs and Bool values in ys. *)
val _ = print_eval "map_fst_eq_alookup_different_value_types"
  ``MAP FST [(strlit "a", 1); (strlit "b", 2)] =
      MAP FST [(strlit "a", T); (strlit "b", F)] /\
    ALOOKUP [(strlit "a", 1); (strlit "b", 2)] (strlit "b") = SOME 2 ==>
    pan_structs$afindi (strlit "b") [(strlit "a", 1); (strlit "b", 2)] = SOME 1 /\
      pan_structs$afindi (strlit "b") [(strlit "a", T); (strlit "b", F)] = SOME 1 /\
      1 < LENGTH [(strlit "a", 1); (strlit "b", 2)] /\
      1 < LENGTH [(strlit "a", T); (strlit "b", F)] /\
      2 = SND (EL 1 [(strlit "a", 1); (strlit "b", 2)]) /\
      ALOOKUP [(strlit "a", T); (strlit "b", F)] (strlit "b") =
        SOME (SND (EL 1 [(strlit "a", T); (strlit "b", F)]))``;
val map_fst_source_type_term =
  ``MAP FST xs = MAP FST ys /\ ALOOKUP xs nm = SOME v``;
val map_fst_inferred_types =
  map (fn variable => term_to_string variable ^
        type_to_string (type_of variable))
    (free_vars map_fst_source_type_term);
val _ = print ("map_fst_eq_alookup_inferred_types=" ^
  String.concatWith "; " map_fst_inferred_types ^ "\n");
