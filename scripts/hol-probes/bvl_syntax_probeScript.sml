load "bossLib"; load "preamble"; load "bvlTheory";
open bossLib HolKernel Parse preamble bvlTheory;
val _ = show_types := true;
val _ = print "exp_case_def=";
val _ = print_term (concl (DB.fetch "bvl" "exp_case_def"));
val _ = print "\n";
val _ = print "exp_nchotomy=";
val _ = print_term (concl (DB.fetch "bvl" "exp_nchotomy"));
val _ = print "\n";
