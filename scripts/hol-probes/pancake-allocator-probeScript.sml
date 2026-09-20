(*
  Focused CakeML allocator probe for one source function.

  Unlike pancake-stage-probeScript.sml this does not print the large
  pan/loop/word/internal terms.  It evaluates the same definitions and emits
  only the selected Word program, its clash tree, Cake's allocator result, and the
  Word-to-Stack result.  This keeps source-to-RISC-V parity investigations
  usable on minimized witnesses without waiting for a multi-megabyte HOL
  pretty-print.

  PANCAKE_SOURCE is required.  PANCAKE_ALLOCATOR_LABEL selects the Word
  function label (default 0); PANCAKE_STAGE_START selects the source entry
  (default main).
*)
load "bossLib";
load "preamble";
load "mlstringSyntax";
load "panPtreeConversionTheory";
load "pan_to_wordTheory";
load "backend_passesTheory";
load "miscTheory";
load "word_to_stackTheory";
load "riscv_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun emit label tm =
  let
    val th = EVAL tm
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n";
    rconc th
  end;

fun evaluate tm = rconc (EVAL tm);

val source_path =
  case OS.Process.getEnv "PANCAKE_SOURCE" of
      SOME path => path
    | NONE => raise Fail "PANCAKE_SOURCE is not set";
val source_file = TextIO.openIn source_path;
val source_text = TextIO.inputAll source_file;
val _ = TextIO.closeIn source_file;
val source_tm = stringSyntax.fromMLstring source_text;
val parsed = evaluate (mk_comb (``parse_topdecs_to_ast``, source_tm));
val (ast, _) =
  if sumSyntax.is_inl parsed then sumSyntax.dest_inl parsed
  else raise Fail "Cake parser rejected source";
val simp = evaluate (mk_comb (``pan_simp$compile_prog``, ast));
val structs = evaluate (mk_comb (``pan_structs$compile_top``, simp));
val start_name =
  case OS.Process.getEnv "PANCAKE_STAGE_START" of
      SOME name => name
    | NONE => "main";
val start_tm = mlstringSyntax.mk_mlstring start_name;
val globals = evaluate
  (list_mk_comb (``pan_globals$compile_top``,
    [structs, start_tm]));
val crep = evaluate (mk_comb (``pan_to_crep$compile_prog``, globals));
val loop = evaluate
  (list_mk_comb (``crep_to_loop$compile_prog``, [``RISC_V``, crep]));

fun filter_label list_tm =
  case OS.Process.getEnv "PANCAKE_ALLOCATOR_LABEL" of
      NONE => list_tm
    | SOME label =>
        let
          val numeral = numSyntax.mk_numeral (Arbnum.fromString label)
          val pred0 = subst [``(0:num)`` |-> numeral]
            ``(λ(item:num # 'a). FST item = 0)``
          val filter_type = type_of ``FILTER``
          val (_, filter_rest) = dom_rng filter_type
          val (filter_list_type, _) = dom_rng filter_rest
          val filter_inst = Term.inst
            (match_type filter_list_type (type_of list_tm)) ``FILTER``
          val (filter_pred_type, _) = dom_rng (type_of filter_inst)
          val pred = Term.inst
            (match_type (type_of pred0) filter_pred_type) pred0
        in
          mk_comb (mk_comb (filter_inst, pred), list_tm)
        end;

val loop_for_word = filter_label loop;
val word = evaluate
  (mk_comb (``loop_to_word$compile``, loop_for_word));
val allocator_label =
  case OS.Process.getEnv "PANCAKE_ALLOCATOR_LABEL" of
      SOME label => Arbnum.fromString label
    | NONE => Arbnum.zero;
val selected_pred0 = subst
  [``(0:num)`` |-> numSyntax.mk_numeral allocator_label]
  ``(λ(name:num,params:num,prog:'a wordLang$prog). name = 0)``;
val filter_type = type_of ``FILTER``;
val (_, filter_rest) = dom_rng filter_type;
val (filter_list_type, _) = dom_rng filter_rest;
val filter_inst = Term.inst
  (match_type filter_list_type (type_of word)) ``FILTER``;
val (filter_pred_type, _) = dom_rng (type_of filter_inst);
val selected_pred = Term.inst
  (match_type (type_of selected_pred0) filter_pred_type) selected_pred0;
val selected_word = mk_comb
  (mk_comb (filter_inst, selected_pred), word);
val internal_fun = ``backend_passes$word_internal_all``;
val internal_config_type = type_of internal_fun |> dom_rng |> fst;
val config_sub = match_type internal_config_type
  (type_of ``riscv_target$riscv_config``);
val selected_word = Term.inst config_sub selected_word;
val internal_fun = Term.inst config_sub internal_fun;
val (_, internal_rest) = dom_rng (type_of internal_fun);
val (internal_ps_type, internal_rest) = dom_rng internal_rest;
val (internal_names_type, _) = dom_rng internal_rest;
val internal_ps = listSyntax.mk_nil
  (internal_ps_type |> dest_type |> snd |> hd);
val internal_names = Term.inst
  (match_type (type_of ``LN``) internal_names_type) ``LN``;
val internal = evaluate
  (list_mk_comb (internal_fun,
    [``riscv_target$riscv_config``, internal_ps,
     internal_names, selected_word]));
val (internal_word, _) = pairSyntax.dest_pair internal;
val selected = internal_word;
val selected_head = fst (listSyntax.dest_cons selected);
val (selected_name, selected_rest) = pairSyntax.dest_pair selected_head;
val (selected_params, selected_prog) = pairSyntax.dest_pair selected_rest;
val clash_fun = Term.inst [Type.alpha |-> ``:64``]
  ``word_alloc$get_clash_tree``;
val clash_term = mk_comb (mk_comb (clash_fun, selected_prog),
  ``([]:(sptree$num_set # sptree$num_set) list)``);
val _ = emit "stage=cake_word_clash_tree" clash_term;
val word_alloc = Term.inst
  [Type.alpha |-> ``:64``] ``word_alloc$word_alloc``;
val none_col = Term.inst
  [Type.alpha |-> ``:num sptree$num_map``] ``NONE``;
val allocated = emit "stage=cake_word_allocated"
  (list_mk_comb (word_alloc,
    [selected_name, ``riscv_target$riscv_config``,
     numSyntax.mk_numeral (Arbnum.fromString "3"),
     numSyntax.mk_numeral (Arbnum.fromString "22"),
     selected_prog, none_col]));
val initial_bitmaps0 = ``(misc$List [4w],1n)``;
val initial_bitmaps = Term.inst
  [Type.alpha |-> ``:64``] initial_bitmaps0;
val word_to_stack = Term.inst
  [Type.alpha |-> ``:64``] ``word_to_stack$compile_prog``;
val stack1 = mk_comb (word_to_stack, ``riscv_target$riscv_config``);
val stack2 = mk_comb (stack1, ``F``);
val stack3 = mk_comb (stack2, allocated);
val stack4 = mk_comb (stack3, selected_params);
val stack5 = mk_comb (stack4,
  numSyntax.mk_numeral (Arbnum.fromString "22"));
val _ = emit "stage=cake_word_to_stack" (mk_comb (stack5, initial_bitmaps));
val _ = emit "stage=cake_word_program" selected;
