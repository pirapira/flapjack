load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val emptyCtx = ``([] : (stcname # struct_info) list)``;
val nameA_f = ``[Name «A» [(«f»,One)] : 8 panLang$decl]``;
val nameA_empty = ``[Name «A» [] : 8 panLang$decl]``;
val dup = ``[Name «A» []; Name «A» [] : 8 panLang$decl]``;
val dupfield = ``[Name «A» [(«f»,One);(«f»,One)] : 8 panLang$decl]``;
val wfmiss = ``[Name «A» [(«f»,Named «Z»)] : 8 panLang$decl]``;
val skip = ``[Decl One «x» (Const (7w:8 word)); Name «A» [] : 8 panLang$decl]``;

val _ = print_eval "dsc_empty" ``(decs_stcnames ^emptyCtx ([] : 8 panLang$decl list) = SOME [])``;
val _ = print_eval "dsc_name_len" ``OPTION_MAP LENGTH (decs_stcnames ^emptyCtx ^nameA_f)``;
val _ = print_eval "dsc_name_size"
  ``OPTION_MAP (\(p : stcname # struct_info). (SND p).size)
       (OPTION_MAP HD (decs_stcnames ^emptyCtx ^nameA_f))``;
val _ = print_eval "dsc_dup" ``(decs_stcnames ^emptyCtx ^dup = NONE)``;
val _ = print_eval "dsc_dupfield" ``(decs_stcnames ^emptyCtx ^dupfield = NONE)``;
val _ = print_eval "dsc_wfmiss" ``(decs_stcnames ^emptyCtx ^wfmiss = NONE)``;
val _ = print_eval "dsc_skip_len" ``OPTION_MAP LENGTH (decs_stcnames ^emptyCtx ^skip)``;