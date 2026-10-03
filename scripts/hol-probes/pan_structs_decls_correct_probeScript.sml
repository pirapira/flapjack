load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsProofTheory;
val _ = Globals.linewidth := 1000000;
val theorem_full = GEN_ALL compile_decls_correct;
val _ = if null(hyp theorem_full) andalso null(free_vars(concl theorem_full)) then () else raise Fail "open theorem";
val _ = print "compile_decls_correct_statement=";
val _ = print_term(concl theorem_full);
val _ = print "\n";
val _ = print("compile_decls_correct_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_full))) ^ "\n");
fun bound_variables tm =
 if is_forall tm then let val (v,b) = dest_forall tm in v :: bound_variables b end
 else if is_conj tm then let val (a,b) = dest_conj tm in bound_variables a @ bound_variables b end
 else [];
val _ = print("compile_decls_correct_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (bound_variables(concl theorem_full))) ^ "\n");
