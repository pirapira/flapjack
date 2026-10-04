(* Original pinned word_depth graph types and values. All rows use exported
original definitions, including arbitrary all_funs metadata; no local replay. *)
load "bossLib"; load "preamble"; load "word_depthTheory";
open bossLib HolKernel Parse preamble word_depthTheory;
val _ = show_types := true;
fun emit label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = print "mk_Branch_type="; val _ = print (type_to_string (type_of ``word_depth$mk_Branch``)); val _ = print "\n";
val _ = emit "mk_Branch_def_typed" (DB.fetch "word_depth" "mk_Branch_def");
val _ = print "call_graph_type="; val _ = print (type_to_string (type_of ``word_depth$call_graph``)); val _ = print "\n";
val _ = emit "call_graph_def_typed" (DB.fetch "word_depth" "call_graph_def");
val _ = print "full_call_graph_type="; val _ = print (type_to_string (type_of ``word_depth$full_call_graph``)); val _ = print "\n";
val _ = emit "full_call_graph_def_typed" (DB.fetch "word_depth" "full_call_graph_def");
val _ = print "max_depth_graphs_type="; val _ = print (type_to_string (type_of ``word_depth$max_depth_graphs``)); val _ = print "\n";
val _ = emit "max_depth_graphs_def_typed" (DB.fetch "word_depth" "max_depth_graphs_def");
fun print_eval label q = (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");
val frame2 = ``insert 2 5 (LN:num num_map)``;
val funs_hit = ``insert 2 (0:num, Skip) (LN:(num # 'a wordLang$prog) num_map)``;
(* mk_Branch absorption and structural cases *)
val _ = print_eval "mb_identity" ``mk_Branch (Leaf:call_tree) Leaf``
val _ = print_eval "mb_leaf_left" ``mk_Branch (Leaf:call_tree) (Const 1 Leaf)``
val _ = print_eval "mb_leaf_right" ``mk_Branch (Const 1 (Leaf:call_tree)) Leaf``
val _ = print_eval "mb_unknown_left" ``mk_Branch (Unknown:call_tree) (Const 1 Leaf)``
val _ = print_eval "mb_unknown_right" ``mk_Branch (Const 1 (Leaf:call_tree)) Unknown``
val _ = print_eval "mb_branch"
  ``mk_Branch (Const 1 (Leaf:call_tree)) (Const 2 Leaf)``

(* call_graph structural and Call cases *)
val _ = print_eval "cg_default"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 5 [] 0 (Skip:'a wordLang$prog)``
val _ = print_eval "cg_seq"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 5 [] 0
      (Seq (Skip:'a wordLang$prog) Skip)``
val _ = print_eval "cg_alloc"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 5 [] 0
      (Alloc 7 ((LN:num_set), (LN:num_set)))``
val _ = print_eval "cg_install"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 5 [] 0
      (Install 0 0 0 0 ((LN:num_set), (LN:num_set)))``
val _ = print_eval "cg_call_dest_none"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 7 [] 0
      (Call NONE NONE [] NONE:'a wordLang$prog)``
val _ = print_eval "cg_call_lookup_miss"
  ``call_graph (LN:(num # 'a wordLang$prog) num_map) 7 [] 0
      (Call NONE (SOME 9) [] NONE:'a wordLang$prog)``
val _ = print_eval "cg_call_tail_hit"
  ``call_graph ^funs_hit 7 [] 1 (Call NONE (SOME 2) [] NONE:'a wordLang$prog)``
val _ = print_eval "cg_call_shortcircuit"
  ``call_graph ^funs_hit 7 [2] 1 (Call NONE (SOME 2) [] NONE:'a wordLang$prog)``
val _ = print_eval "cg_call_guard"
  ``call_graph ^funs_hit 7 [] 0 (Call NONE (SOME 2) [] NONE:'a wordLang$prog)``

(* full_call_graph hit/miss *)
val _ = print_eval "fcg_miss"
  ``full_call_graph 9 (LN:(num # 'a wordLang$prog) num_map)``
val _ = print_eval "fcg_hit" ``full_call_graph 2 ^funs_hit``

(* max_depth_graphs empty / frame hit / frame miss / whole-code miss *)
val _ = print_eval "mdg_empty"
  ``max_depth_graphs (LN:num num_map) [] [] (LN:(num # 'a wordLang$prog) num_map)
      (LN:(num # 'a wordLang$prog) num_map)``
val _ = print_eval "mdg_frame_hit"
  ``max_depth_graphs ^frame2 [2] [] (LN:(num # 'a wordLang$prog) num_map) ^funs_hit``
val _ = print_eval "mdg_frame_miss"
  ``max_depth_graphs (LN:num num_map) [2] [] (LN:(num # 'a wordLang$prog) num_map) ^funs_hit``
val _ = print_eval "mdg_code_miss"
  ``max_depth_graphs (LN:num num_map) [9] [] (LN:(num # 'a wordLang$prog) num_map)
      (LN:(num # 'a wordLang$prog) num_map)``

(* Source return/handler, structural descent and recursion cases. *)
val cuts = ``((LN:num_set), (LN:num_set))``;
val _ = print_eval "cg_if" ``call_graph ^funs_hit 3 [] 1 (If Equal 0 (Reg 0) (Alloc 7 ^cuts) Skip:'a wordLang$prog)``;
val _ = print_eval "cg_must_terminate" ``call_graph ^funs_hit 3 [] 1 (MustTerminate (Alloc 7 ^cuts):'a wordLang$prog)``;
val _ = print_eval "cg_loop" ``call_graph ^funs_hit 3 [] 1 (Loop (LN:num_set) (Alloc 7 ^cuts) (LN:num_set):'a wordLang$prog)``;
val _ = print_eval "cg_return" ``call_graph ^funs_hit 1 [] 1 (Call (SOME ([],^cuts,Skip,0,0)) (SOME 2) [] NONE:'a wordLang$prog)``;
val _ = print_eval "cg_handler" ``call_graph ^funs_hit 1 [] 1 (Call (SOME ([],^cuts,Skip,0,0)) (SOME 2) [] (SOME (0,Skip,0,0)):'a wordLang$prog)``;
val tail_self = ``insert 1 (0:num,Call NONE (SOME 1) [] NONE:'a wordLang$prog) (LN:(num # 'a wordLang$prog) num_map)``;
val ret_self = ``insert 1 (0:num,Call (SOME ([],^cuts,Skip,0,0)) (SOME 1) [] NONE:'a wordLang$prog) (LN:(num # 'a wordLang$prog) num_map)``;
val mutual = ``insert 1 (0:num,Call NONE (SOME 2) [] NONE:'a wordLang$prog) (insert 2 (0:num,Call NONE (SOME 1) [] NONE:'a wordLang$prog) (LN:(num # 'a wordLang$prog) num_map))``;
val _ = print_eval "fcg_tail_self" ``full_call_graph 1 ^tail_self``;
val _ = print_eval "fcg_ret_self" ``full_call_graph 1 ^ret_self``;
val _ = print_eval "fcg_mutual" ``full_call_graph 1 ^mutual``;
val _ = print_eval "mdg_recursive" ``max_depth_graphs (insert 1 4 (LN:num num_map)) [1] [] ^tail_self ^tail_self``;
(* The unused metadata is independent: Bool and list carriers. *)
val _ = print_eval "mdg_bool_metadata" ``max_depth_graphs ^frame2 [2] [] (LN:(num # 'a wordLang$prog) num_map) (insert 2 (T,Skip) (LN:(bool # 'a wordLang$prog) num_map))``;
val _ = print_eval "mdg_list_metadata" ``max_depth_graphs ^frame2 [2] [] (LN:(num # 'a wordLang$prog) num_map) (insert 2 ([3;4],Skip) (LN:(num list # 'a wordLang$prog) num_map))``;
