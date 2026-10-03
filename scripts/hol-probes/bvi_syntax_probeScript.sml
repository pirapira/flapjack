load "bossLib"; load "preamble"; load "bviTheory";
open bossLib HolKernel Parse preamble bviTheory;
val _ = show_types := true;
val _ = print "exp_case_def=";
val _ = print_term (concl (DB.fetch "bvi" "exp_case_def"));
val _ = print "\n";
val _ = print "exp_nchotomy=";
val _ = print_term (concl (DB.fetch "bvi" "exp_nchotomy"));
val _ = print "\n";
