(* pan_lang_decl_probe: direct HOL oracle for the exact panLang fun_decl / decl /
   struct_info carriers (bead flapjack-pxn.18.3.5.8.4).

   Source: cakeml/pancake/panLangScript.sml:102-122 (fun_decl record, decl
   datatype, struct_info record). Names varname/fldname/stcname/eid are mlstring.

   Provenance: read-only prebuilt oracle checkout /home/zksecurity/flapjack2/cakeml
   (cakeml submodule HEAD 857f0d98da8f8a3580f34423338e697809308ede, the same
   commit as the flap-ds2 submodule); the flap-ds2 checkout has no built HOL
   theories. Regenerate with:
     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=pan_lang_decl_probeScript.sml timeout 250 \
       scripts/hol-probes/regenerate.sh </dev/null
   Explicit type annotations are required or EVAL leaves the word width symbolic. *)

load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

val _ = print_eval "fd_name_len"
  ``(case (<| name := strlit "AB"; inline := T; export := F;
             params := [(strlit "x", One); (strlit "y", One)];
             body := Skip; return := One |>
          : 64 fun_decl) of fd => strlen fd.name)``;
val _ = print_eval "fd_inline"
  ``(case (<| name := strlit "AB"; inline := T; export := F;
             params := [(strlit "x", One)];
             body := Skip; return := One |> : 64 fun_decl) of fd => fd.inline)``;
val _ = print_eval "fd_export"
  ``(case (<| name := strlit "AB"; inline := T; export := F;
             params := [(strlit "x", One)];
             body := Skip; return := One |> : 64 fun_decl) of fd => fd.export)``;
val _ = print_eval "fd_params_len"
  ``(case (<| name := strlit "AB"; inline := T; export := F;
             params := [(strlit "x", One); (strlit "y", One)];
             body := Skip; return := One |> : 64 fun_decl) of fd => LENGTH fd.params)``;
val _ = print_eval "fd_body_is_skip"
  ``(case (<| name := strlit "AB"; inline := T; export := F;
             params := []; body := Skip; return := One |> : 64 fun_decl) of fd => (fd.body = Skip))``;
val _ = print_eval "d_function_name_len"
  ``(case (Function (<| name := strlit "AB"; inline := T; export := F;
                       params := []; body := Skip; return := One |> : 64 fun_decl)
          : 64 decl) of Function fd => strlen fd.name | _ => 0)``;
val _ = print_eval "d_decl_name_len"
  ``(case (Decl One (strlit "z") (Const (5w : 64 word)) : 64 decl) of
       Decl _ nm _ => strlen nm | _ => 0)``;
val _ = print_eval "d_exn_name_len"
  ``(case (ExnDecl (strlit "ex") One : 64 decl) of
       ExnDecl eid _ => strlen eid | _ => 0)``;
val _ = print_eval "d_name_fields_len"
  ``(case (Name (strlit "S") [(strlit "f", One)] : 64 decl) of
       Name _ flds => LENGTH flds | _ => 0)``;
val _ = print_eval "si_fields_len"
  ``(case (<| fields := [(strlit "f", One)]; size := 7 |> : struct_info) of
       si => LENGTH si.fields)``;
val _ = print_eval "si_size"
  ``(case (<| fields := []; size := 7 |> : struct_info) of si => si.size)``;