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
