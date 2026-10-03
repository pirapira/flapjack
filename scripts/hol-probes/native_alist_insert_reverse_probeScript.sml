load "preamble"; load "miscTheory";
open HolKernel Parse bossLib preamble miscTheory sptreeTheory;
val _ = Globals.linewidth := 1000000;
val result = GEN_ALL(prove(``
   ∀xs ys s.
   ALL_DISTINCT xs ∧ LENGTH xs = LENGTH ys ⇒
   alist_insert (REVERSE xs) (REVERSE ys) s = alist_insert xs ys s``,
  Induct \\ simp[alist_insert_def]
  \\ gen_tac \\ Cases \\ simp[alist_insert_def]
  \\ simp[alist_insert_append,alist_insert_def]
  \\ rw[] \\ simp[alist_insert_pull_insert]));
val _ = if null(hyp result) andalso null(free_vars(concl result)) then () else raise Fail "open reversal";
val _ = (print "alistInsertReverse_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl result));
val _ = print("alistInsertReverse_proved=" ^ term_to_string(rhs(concl(EQT_INTRO result))) ^ "\n");
val _ = print("alistInsertReverse_hypotheses=" ^ Int.toString(length(hyp result)) ^ "\n");
