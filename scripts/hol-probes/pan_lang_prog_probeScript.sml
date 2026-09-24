load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL over the `panLang$prog` datatype
   (cakeml/pancake/panLangScript.sml:78-100):

     prog = Skip | Dec varname shape ('a exp) prog | Assign varkind varname ('a exp)
          | Primitive varname primop ('a exp list)
          | Store/Store32/StoreByte ('a exp) ('a exp) | Seq prog prog
          | If ('a exp) prog prog | While ('a exp) prog | Break | Continue
          | Call (((varkind # varname) option # ((eid # varname # prog) option)) option)
              funname ('a exp list)
          | DecCall varname shape funname ('a exp list) prog
          | ExtCall funname ('a exp) ('a exp) ('a exp) ('a exp)
          | Raise eid ('a exp) | Return ('a exp)
          | ShMemLoad opsize varkind varname ('a exp)
          | ShMemStore opsize ('a exp) ('a exp) | Tick | Annot mlstring mlstring

   where varname/funname/eid/stcname/fldname are `mlstring` (lines 23-31).  The
   executable `Flapjack.Prog alpha` is generic over the word type and uses Lean
   `String` identifiers, so it is untagged.  The exact counterpart
   `Flapjack.Pancake.PanLang.ProgHOL width` uses `BitVec width` payloads and the
   faithful `MlString` carrier for identifiers.

   The rows below pin the name fields as `mlstring`, the word-indexed exp
   payloads, and representative constructor arities at the HOL numeral word type
   64.

   Provenance: generated from the Flapjack checkout with the
   coordinator-approved read-only prebuilt CakeML/HOL object directory as oracle
   input, without editing that checkout.  `panLangTheory` is prebuilt in
   flapjack2/3/4/6:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=pan_lang_prog_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede. *)

val _ = print_eval "pg_skip"
  ``(case (Skip : 64 prog) of Skip => 1 | _ => 0)``;
val _ = print_eval "pg_dec_name_len"
  ``(case (Dec (strlit "x") One (Const (5w : 64 word)) Skip : 64 prog) of
       Dec nm _ _ _ => strlen nm | _ => 0)``;
val _ = print_eval "pg_assign_kind"
  ``(case (Assign Local (strlit "x") (Const (5w : 64 word)) : 64 prog) of
       Assign k _ _ => (case k of Local => 0 | Global => 1) | _ => 2)``;
val _ = print_eval "pg_primitive_args_len"
  ``(case (Primitive (strlit "x") AddCarry
             [Const (1w : 64 word); Const (2w : 64 word)] : 64 prog) of
       Primitive _ _ es => LENGTH es | _ => 0)``;
val _ = print_eval "pg_store"
  ``(case (Store (Const (1w : 64 word)) (Const (2w : 64 word)) : 64 prog) of
       Store _ _ => 1 | _ => 0)``;
val _ = print_eval "pg_seq"
  ``(case (Seq Skip Skip : 64 prog) of Seq _ _ => 1 | _ => 0)``;
val _ = print_eval "pg_if"
  ``(case (If (Const (1w : 64 word)) Skip Skip : 64 prog) of If _ _ _ => 1 | _ => 0)``;
val _ = print_eval "pg_while"
  ``(case (While (Const (1w : 64 word)) Skip : 64 prog) of While _ _ => 1 | _ => 0)``;
val _ = print_eval "pg_break"
  ``(case (Break : 64 prog) of Break => 1 | _ => 0)``;
val _ = print_eval "pg_continue"
  ``(case (Continue : 64 prog) of Continue => 1 | _ => 0)``;
val _ = print_eval "pg_call_args_len"
  ``(case (Call NONE (strlit "f") [Const (1w : 64 word)] : 64 prog) of
       Call _ nm es => LENGTH es + strlen nm | _ => 0)``;
val _ = print_eval "pg_deccall_args_len"
  ``(case (DecCall (strlit "x") One (strlit "f")
             [Const (1w : 64 word)] Skip : 64 prog) of
       DecCall nm _ _ es _ => LENGTH es + strlen nm | _ => 0)``;
val _ = print_eval "pg_extcall_name_len"
  ``(case (ExtCall (strlit "ffi")
             (Const (1w : 64 word)) (Const (2w : 64 word))
             (Const (3w : 64 word)) (Const (4w : 64 word)) : 64 prog) of
       ExtCall nm _ _ _ _ => strlen nm | _ => 0)``;
val _ = print_eval "pg_raise_eid_len"
  ``(case (Raise (strlit "ex") (Const (1w : 64 word)) : 64 prog) of
       Raise eid _ => strlen eid | _ => 0)``;
val _ = print_eval "pg_return"
  ``(case (Return (Const (1w : 64 word)) : 64 prog) of Return _ => 1 | _ => 0)``;
val _ = print_eval "pg_shmemload_size"
  ``(case (ShMemLoad OpW Local (strlit "x") (Const (1w : 64 word)) : 64 prog) of
       ShMemLoad sz _ _ _ => (case sz of Op8 => 0 | OpW => 1 | Op32 => 2 | Op16 => 3) | _ => 4)``;
val _ = print_eval "pg_shmemstore"
  ``(case (ShMemStore Op32 (Const (1w : 64 word)) (Const (2w : 64 word)) : 64 prog) of
       ShMemStore _ _ _ => 1 | _ => 0)``;
val _ = print_eval "pg_tick"
  ``(case (Tick : 64 prog) of Tick => 1 | _ => 0)``;
val _ = print_eval "pg_annot_len"
  ``(case (Annot (strlit "tag") (strlit "txt") : 64 prog) of
       Annot a b => strlen a + strlen b | _ => 0)``;