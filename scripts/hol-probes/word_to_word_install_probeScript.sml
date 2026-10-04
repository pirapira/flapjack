load "preamble";
load "word_to_wordProofTheory";
open HolKernel Parse bossLib preamble word_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun emit label th =
  let val closed = GEN_ALL th in
    if null(hyp closed) andalso null(free_vars(concl closed)) then () else raise Fail "open original theorem";
    print(label ^ "=" ^ term_to_string(concl closed) ^ "\n")
  end;
val _ = emit "compile_single_correct_typed" compile_single_correct;
val core = SPEC_ALL compile_single_correct;
val progVar = valOf(List.find (fn v => fst(dest_var v) = "prog") (free_vars(concl core)));
val install = ``(wordLang$Install ptr len dptr dlen names : 'a wordLang$prog)``;
val (ts, tys) = match_term progVar install;
val installThm = INST ts (INST_TYPE tys core);
val _ = emit "compile_single_correct_install_typed" installThm;
val _ = print("compile_single_correct_install_hypotheses=" ^ Int.toString(length(hyp installThm)) ^ "\n");
