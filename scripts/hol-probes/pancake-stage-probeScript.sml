(*
  Dynamic intermediate-stage probe for one Pancake source file.

  PANCAKE_SOURCE names a file containing source text.  This is deliberately
  evaluated by the original CakeML HOL definitions; the companion
  `flapjack-debug` executable prints the corresponding Lean stages.
*)
load "bossLib";
load "preamble";
load "panPtreeConversionTheory";
load "pan_to_wordTheory";
load "backend_passesTheory";
load "riscv_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun eval_term label tm =
  let
    val th = EVAL tm
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n";
    rconc th
  end;

val source_path =
  case OS.Process.getEnv "PANCAKE_SOURCE" of
      SOME path => path
    | NONE => raise Fail "PANCAKE_SOURCE is not set";
val source_file = TextIO.openIn source_path;
val source_text = TextIO.inputAll source_file;
val _ = TextIO.closeIn source_file;
val source_tm = stringSyntax.fromMLstring source_text;
val parsed = eval_term "stage=parsed_result"
  (mk_comb (``parse_topdecs_to_ast``, source_tm));

val (ast, _) =
  if sumSyntax.is_inl parsed then sumSyntax.dest_inl parsed
  else raise Fail "Cake parser rejected source; inspect stage=parsed_result";
val simp = eval_term "stage=pan_simp"
  (mk_comb (``pan_simp$compile_prog``, ast));
val structs = eval_term "stage=pan_structs"
  (mk_comb (``pan_structs$compile_top``, simp));
val start_tm = ``«main»``;
val globals_term = list_mk_comb (``pan_globals$compile_top``, [structs, start_tm]);
val _ = print ("globals_type=" ^ type_to_string (type_of globals_term) ^ "\n");
val globals = eval_term "stage=pan_globals"
  globals_term;
val crep = eval_term "stage=pan_to_crep"
  (mk_comb (``pan_to_crep$compile_prog``, globals));
val loop = eval_term "stage=crep_to_loop"
  (list_mk_comb (``crep_to_loop$compile_prog``, [``RISC_V``, crep]));
val word = eval_term "stage=loop_to_word"
  (mk_comb (``loop_to_word$compile``, loop));

(* Optional focused probe for comparing the inputs to word_alloc.  The
   complete word program above is useful for ordinary stage debugging, but
   allocator parity needs the original heuristic and stack-only inputs too.
   Keep this opt-in because these terms can be large. *)
val _ =
  case OS.Process.getEnv "PANCAKE_ALLOCATOR_PROBE" of
      NONE => ()
    | SOME _ =>
        let
          val allocator_target =
            case OS.Process.getEnv "PANCAKE_ALLOCATOR_LABEL" of
                SOME label => Arbnum.fromString label
              | NONE => Arbnum.zero
          val selected_pred0 = subst
            [``(0:num)`` |-> numSyntax.mk_numeral allocator_target]
            ``(λ(name:num,params:num,prog:'a wordLang$prog). name = 0)``
          val filter_type = type_of ``FILTER``
          val (_, filter_rest) = dom_rng filter_type
          val (filter_list_type, _) = dom_rng filter_rest
          val filter_inst = Term.inst
            (match_type filter_list_type (type_of word)) ``FILTER``
          val (filter_pred_type, _) = dom_rng (type_of filter_inst)
          val selected_pred = Term.inst
            (match_type (type_of selected_pred0) filter_pred_type) selected_pred0
          val selected_word = mk_comb
            (mk_comb (filter_inst, selected_pred), word)
          val internal_fun = ``backend_passes$word_internal_all``
          val internal_config_type = type_of internal_fun |> dom_rng |> fst
          val config_sub = match_type internal_config_type
            (type_of ``riscv_target$riscv_config``)
          val selected_word = Term.inst config_sub selected_word
          val internal_fun = Term.inst config_sub internal_fun
          val (_, internal_rest) = dom_rng (type_of internal_fun)
          val (internal_ps_type, internal_rest) = dom_rng internal_rest
          val (internal_names_type, _) = dom_rng internal_rest
          val internal_ps = listSyntax.mk_nil
            (internal_ps_type |> dest_type |> snd |> hd)
          val internal_names = Term.inst
            (match_type (type_of ``LN``) internal_names_type) ``LN``
          val internal = eval_term "stage=word_internal_all"
            (list_mk_comb (internal_fun,
              [``riscv_target$riscv_config``, internal_ps,
               internal_names, selected_word]))
          val (internal_word, _) = pairSyntax.dest_pair internal
          val selected = internal_word
          val selected_entry_type = type_of selected |> dest_type |> snd |> hd
          val map_inst = Term.inst
            [Type.alpha |-> selected_entry_type] ``MAP``
          val input_pred0 = ``(λ(name:num,params:num,prog:'a wordLang$prog).
            (name, word_alloc$get_heuristics 3 0 prog,
             word_alloc$get_stack_only prog))``
          val input_pred = Term.inst
            [Type.alpha |->
             (selected_entry_type |> dest_type |> snd |> List.last
              |> dest_type |> snd |> List.last
              |> dest_type |> snd |> List.last)] input_pred0
          val map_inst_typed = Term.inst
            [Type.beta |-> (type_of input_pred |> dom_rng |> snd)] map_inst
          val input_term = mk_comb
            (mk_comb (map_inst_typed, input_pred), selected)
        in
          ignore (eval_term "stage=cake_word_allocator_input" selected);
          ignore (eval_term "stage=cake_word_heuristics" input_term)
        end
