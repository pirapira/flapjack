load "bossLib";
load "preamble";
load "crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL over the `crepLang$prog` datatype
   (cakeml/pancake/crepLangScript.sml:41-66):

     prog = Skip | Dec varname ('a exp) prog | Assign varname ('a exp) |
       Primitive (varname list) panLang$primop (varname list) |
       Store ('a exp) ('a exp) | Store32 | StoreByte ('a exp) ('a exp) |
       StoreGlob (5 word) ('a exp) | Seq prog prog | If ('a exp) prog prog |
       While ('a exp) prog | Break num | Continue num |
       Call (((varname list) # ((('a word) # prog) option)) option)
            funname (('a exp) list) |
       ExtCall funname varname varname varname varname | Raise ('a word) |
       Return (('a exp) list) | ShMem memop varname ('a exp) | Tick

   where varname is `num`, funname is `mlstring`, the word payloads are
   `'a word` (plus the fixed `5 word` in StoreGlob), and `memop` is `asm$memop`.

   The executable `Flapjack.CrepProg alpha` uses `String` function names and is
   untagged; the exact counterpart `Flapjack.CrepProgHOL width` uses `BitVec
   width` and `MlString` names.

   Rows pin the word payloads, name lengths, and arities at the HOL numeral word
   type 8.

   Provenance: generated from the Flapjack checkout with the coordinator-approved
   read-only prebuilt CakeML/HOL object directory as oracle input, without
   editing that checkout:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=crep_lang_prog_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   cakeml submodule HEAD 857f0d98da8f8a3580f34423338e697809308ede. *)
val _ = print_eval "prg_skip"
  ``(case (crepLang$Skip : 8 crepLang$prog) of crepLang$Skip => 1 | _ => 0)``;
val _ = print_eval "prg_dec"
  ``(case (crepLang$Dec 3 (crepLang$Const (5w : 8 word)) crepLang$Skip
          : 8 crepLang$prog) of crepLang$Dec n _ _ => n | _ => 0)``;
val _ = print_eval "prg_assign"
  ``(case (crepLang$Assign 4 (crepLang$Const (5w : 8 word))
          : 8 crepLang$prog) of crepLang$Assign n _ => n | _ => 0)``;
val _ = print_eval "prg_primitive"
  ``(case (crepLang$Primitive [1;2] panLang$AddCarry [3]
          : 8 crepLang$prog) of
       crepLang$Primitive ns _ ms => LENGTH ns + LENGTH ms | _ => 0)``;
val _ = print_eval "prg_store"
  ``(case (crepLang$Store (crepLang$Const (1w : 8 word))
            (crepLang$Const (2w : 8 word)) : 8 crepLang$prog) of
       crepLang$Store _ _ => 1 | _ => 0)``;
val _ = print_eval "prg_store32"
  ``(case (crepLang$Store32 (crepLang$Const (1w : 8 word))
            (crepLang$Const (2w : 8 word)) : 8 crepLang$prog) of
       crepLang$Store32 _ _ => 1 | _ => 0)``;
val _ = print_eval "prg_storebyte"
  ``(case (crepLang$StoreByte (crepLang$Const (1w : 8 word))
            (crepLang$Const (2w : 8 word)) : 8 crepLang$prog) of
       crepLang$StoreByte _ _ => 1 | _ => 0)``;
val _ = print_eval "prg_storeglob"
  ``(case (crepLang$StoreGlob (7w : 5 word) (crepLang$Const (1w : 8 word))
          : 8 crepLang$prog) of crepLang$StoreGlob w _ => w2n w | _ => 0)``;
val _ = print_eval "prg_seq"
  ``(case (crepLang$Seq crepLang$Skip crepLang$Skip : 8 crepLang$prog) of
       crepLang$Seq _ _ => 1 | _ => 0)``;
val _ = print_eval "prg_if"
  ``(case (crepLang$If (crepLang$Const (1w : 8 word)) crepLang$Skip crepLang$Skip
          : 8 crepLang$prog) of crepLang$If _ _ _ => 1 | _ => 0)``;
val _ = print_eval "prg_while"
  ``(case (crepLang$While (crepLang$Const (1w : 8 word)) crepLang$Skip
          : 8 crepLang$prog) of crepLang$While _ _ => 1 | _ => 0)``;
val _ = print_eval "prg_break"
  ``(case (crepLang$Break 5 : 8 crepLang$prog) of crepLang$Break n => n | _ => 0)``;
val _ = print_eval "prg_continue"
  ``(case (crepLang$Continue 6 : 8 crepLang$prog) of
       crepLang$Continue n => n | _ => 0)``;
val _ = print_eval "prg_call_args_len"
  ``(case (crepLang$Call NONE (strlit "f") [crepLang$Const (1w : 8 word)]
          : 8 crepLang$prog) of crepLang$Call _ _ args => LENGTH args | _ => 0)``;
val _ = print_eval "prg_extcall_name_len"
  ``(case (crepLang$ExtCall (strlit "g") 1 2 3 4 : 8 crepLang$prog) of
       crepLang$ExtCall f _ _ _ _ => strlen f | _ => 0)``;
val _ = print_eval "prg_raise"
  ``(case (crepLang$Raise (5w : 8 word) : 8 crepLang$prog) of
       crepLang$Raise w => w2n w | _ => 0)``;
val _ = print_eval "prg_return_len"
  ``(case (crepLang$Return [crepLang$Const (1w : 8 word);
                            crepLang$Const (2w : 8 word)]
          : 8 crepLang$prog) of crepLang$Return es => LENGTH es | _ => 0)``;
val _ = print_eval "prg_shmem"
  ``(case (crepLang$ShMem asm$Load8 3 (crepLang$Const (1w : 8 word))
          : 8 crepLang$prog) of crepLang$ShMem _ n _ => n | _ => 0)``;
val _ = print_eval "prg_tick"
  ``(case (crepLang$Tick : 8 crepLang$prog) of crepLang$Tick => 1 | _ => 0)``;
