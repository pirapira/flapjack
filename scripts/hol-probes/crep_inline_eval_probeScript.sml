(* Direct HOL-EVAL observations for `crepSem$eval` over a pair of Crep states
   that share locals and `state_rel_code` but have DIFFERENT nonempty code maps
   related by the finite-map `code_inl_rel` pattern
   (crep_inlineProofScript.sml:1504): the target `main` body is the inlined
   `Seq Tick Skip` produced from the source `Call NONE «inc» []`.

   References:
     cakeml/pancake/semantics/crepSemScript.sml:20-143: state record and eval
     cakeml/pancake/semantics/crepSemScript.sml:90: eval_def
     cakeml/pancake/crep_inlineScript.sml:203: inline_prog (target body) *)

load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val srcCode =
  ``alist_to_fmap
      [(«main», ([7], (Call NONE «inc» [] : 64 crepLang$prog)));
       («inc», ([8], (Skip : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;
val tgtCode =
  ``alist_to_fmap
      [(«main», ([7], (Seq Tick Skip : 64 crepLang$prog)));
       («inc», ([8], (Skip : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;

fun mkState code =
  ``(<| locals := (FEMPTY |+ (0, Word (7w:64 word)));
        globals := FEMPTY;
        code := ^code;
        memory := K (Word (0w:64 word));
        memaddrs := {};
        sh_memaddrs := {};
        clock := 5;
        be := F;
        ffi := ARB;
        base_addr := (0w:64 word);
        top_addr := (100w:64 word) |> : (64, unit) crepSem$state)``;

val s = mkState srcCode;
val t = mkState tgtCode;

val _ = print_eval "src_main_is_call"
  ``case FLOOKUP ^srcCode «main» of
      SOME (_, Call NONE _ _) => T | _ => F``;
val _ = print_eval "tgt_main_is_tail"
  ``case FLOOKUP ^tgtCode «main» of
      SOME (_, Seq Tick _) => T | _ => F``;
val _ = print_eval "code_keys_nonempty"
  ``(FLOOKUP ^srcCode «inc» <> NONE) /\ (FLOOKUP ^tgtCode «inc» <> NONE)``;
val _ = print_eval "src_var"
  ``case eval ^s (Var (0:num)) of SOME (Word w) => (w = (7w:64 word)) | _ => F``;
val _ = print_eval "tgt_var"
  ``case eval ^t (Var (0:num)) of SOME (Word w) => (w = (7w:64 word)) | _ => F``;
val _ = print_eval "src_var_eq_tgt_var"
  ``eval ^s (Var (0:num)) = eval ^t (Var (0:num))``;
