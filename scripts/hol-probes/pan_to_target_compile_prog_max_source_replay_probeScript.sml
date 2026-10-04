(* Literal full source-definition replay of pan_to_targetProof1147-1155.
The original proof theory is unbuilt; all named pass dependencies below are
loaded original theories. This is not an exported original-theory capture. *)
load "bossLib"; load "preamble"; load "pan_to_targetTheory";
load "targetSemTheory"; load "word_depthTheory";
open bossLib HolKernel Parse preamble pan_to_targetTheory targetSemTheory word_depthTheory;
(* Fail rather than capture a stale literal if the pinned source changes. *)
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "pancake/proofs/pan_to_targetProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;
val _ = if String.isSubstring "Definition compile_prog_max_def:\n  compile_prog_max c mc prog =\n    let asm_conf = mc.target.config in\n    let prog = pan_to_word$compile_prog asm_conf.ISA prog in\n    let (col,wprog) = word_to_word$compile c.word_to_word_conf asm_conf prog in\n    let (bm,c',fs,p) = word_to_stack$compile asm_conf F wprog in\n    let max = max_depth c'.stack_frame_size (full_call_graph InitGlobals_location (fromAList wprog)) in\n      (from_stack asm_conf c LN p bm, max)\nEnd" source_text
  then () else raise Fail "compile_prog_max literal source changed";

val _ = new_theory "flapjack_compile_prog_max_source_replay";
val compile_prog_max_source_def = Define `
  compile_prog_max c mc prog =
    let asm_conf = mc.target.config in
    let prog = pan_to_word$compile_prog asm_conf.ISA prog in
    let (col,wprog) = word_to_word$compile c.word_to_word_conf asm_conf prog in
    let (bm,c',fs,p) = word_to_stack$compile asm_conf F wprog in
    let max = max_depth c'.stack_frame_size (full_call_graph InitGlobals_location (fromAList wprog)) in
      (from_stack asm_conf c LN p bm, max)
`;
val _ = show_types := true;
val _ = print "compile_prog_max_local_replay_type=";
val _ = print (type_to_string (type_of ``compile_prog_max``));
val _ = print "\n";
val _ = print "compile_prog_max_local_replay_def_typed=";
val _ = print_term (concl compile_prog_max_source_def);
val _ = print "\n";
