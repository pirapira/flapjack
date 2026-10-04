load "preamble";
load "pan_to_targetTheory";
open HolKernel Parse bossLib preamble pan_to_targetTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun emit label th =
  let val full = GEN_ALL th in
    if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
    print(label ^ "=" ^ term_to_string(concl full) ^ "\n")
  end;
val _ = emit "exports_def" exports_def;
val _ = emit "compile_prog_def" compile_prog_def;
val _ = print("exports_type=" ^ type_to_string(type_of ``pan_to_target$exports``) ^ "\n");
val _ = print("compile_prog_type=" ^ type_to_string(type_of ``pan_to_target$compile_prog``) ^ "\n");
val _ = emit "zip_def" listTheory.ZIP_def;
val _ = emit "splitp_def" rich_listTheory.SPLITP;
val full = SPEC_ALL compile_prog_def;
val firstMain = snd(dest_comb(rhs(concl full)));
val programVar = mk_var("prog", type_of firstMain);
(* Extract the original first LET argument, not a separately retyped replay. *)
val _ = print("compile_prog_main_binding=" ^ term_to_string firstMain ^ "\n");
fun mainNames label program =
  let val (ts,tys) = match_term programVar program;
      val instantiated = subst ts (inst tys firstMain);
      val observed = ``MAP FST (panLang$functions ^instantiated)``
  in print(label ^ "=" ^ term_to_string(rhs(concl(EVAL observed))) ^ "\n") end;
val _ = mainNames "main_empty_names" ``([] :'a decl list)``;
val _ = mainNames "main_missing_names" ``[ExnDecl «E» One] :'a decl list``;
val _ = mainNames "main_already_first_names" ``[Function <|name := «main»; inline := F; export := F; params := []; body := Return(Const 0w); return := One|>; ExnDecl «E» One] :'a decl list``;
val _ = mainNames "main_later_names" ``[ExnDecl «E» One; Function <|name := «main»; inline := F; export := F; params := []; body := Return(Const 0w); return := One|>] :'a decl list``;
val _ = mainNames "main_nonempty_missing_names" ``[Function <|name := «f»; inline := F; export := F; params := []; body := Return(Const 0w); return := One|>; Function <|name := «g»; inline := F; export := F; params := []; body := Return(Const 0w); return := One|>] :'a decl list``;
val _ = mainNames "main_first_only_duplicates_names" ``[Function <|name := «f»; inline := F; export := F; params := []; body := Return(Const 0w); return := One|>; Function <|name := «main»; inline := F; export := F; params := []; body := Return(Const 0w); return := One|>; Function <|name := «g»; inline := F; export := F; params := []; body := Return(Const 0w); return := One|>; Function <|name := «main»; inline := F; export := T; params := []; body := Return(Const 0w); return := One|>] :'a decl list``;
val _ = print("exports_empty=" ^ term_to_string(rhs(concl(EVAL ``pan_to_target$exports ([] :'a decl list)``))) ^ "\n");
val _ = print("exports_flags_duplicates=" ^ term_to_string(rhs(concl(EVAL ``pan_to_target$exports ([Function <|name := «f»; inline := F; export := T; params := []; body := Return(Const 0w); return := One|>; ExnDecl «E» One; Function <|name := «hidden»; inline := F; export := F; params := []; body := Return(Const 0w); return := One|>; Function <|name := «f»; inline := F; export := T; params := []; body := Return(Const 0w); return := One|>] :'a decl list)``))) ^ "\n");
