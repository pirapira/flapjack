load "preamble"; load "riscvTheory";
open HolKernel Parse bossLib preamble riscvTheory;
val _ = computeLib.add_funs [Encode_def, Utype_def, opc_def, Decode_def, boolify32_def];
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
(* Finite original boundaries only; unrestricted Lean proofs and source
   comparison are separate obligations. No exhaustive equivalence claim. *)
fun out label tm = (print(label ^ "="); print_term(rhs(concl(EVAL tm))); print "\n");
fun replay label tm =
  (print (label ^ "="); print_term tm; print "\n");
val _ = out "lui_decode_zero" ``Decode (Encode (ArithI (LUI (0w,0w)))) = ArithI (LUI (0w,0w))``;
val _ = out "lui_decode_all_ones" ``Decode (Encode (ArithI (LUI (31w,1048575w)))) = ArithI (LUI (31w,1048575w))``;
val _ = out "lui_decode_sign_bit" ``Decode (Encode (ArithI (LUI (1w,524288w)))) = ArithI (LUI (1w,524288w))``;
val _ = out "lui_decode_positive_max" ``Decode (Encode (ArithI (LUI (0w,524287w)))) = ArithI (LUI (0w,524287w))``;
val _ = out "auipc_decode_zero" ``Decode (Encode (ArithI (AUIPC (0w,0w)))) = ArithI (AUIPC (0w,0w))``;
val _ = out "auipc_decode_all_ones" ``Decode (Encode (ArithI (AUIPC (31w,1048575w)))) = ArithI (AUIPC (31w,1048575w))``;
val _ = out "auipc_decode_sign_bit" ``Decode (Encode (ArithI (AUIPC (1w,524288w)))) = ArithI (AUIPC (1w,524288w))``;
val _ = out "auipc_decode_positive_max" ``Decode (Encode (ArithI (AUIPC (0w,524287w)))) = ArithI (AUIPC (0w,524287w))``;
val _ = (print "upper_decode_source_clause="; print "HOL riscvScript.sml Encode_def / Decode_def with Utype_def (LUI,AUIPC); local compositions, no named source theorem."; print "\n");
val _ = replay "upper_decode_replay" ``(!(rd:word5) (imm:word20). Decode (Encode (ArithI (LUI (rd,imm)))) = ArithI (LUI (rd,imm))) /\ (!(rd:word5) (imm:word20). Decode (Encode (ArithI (AUIPC (rd,imm)))) = ArithI (AUIPC (rd,imm)))``;
val _ = print ("upper_decode_carriers=" ^ String.concatWith ", " (map (fn (n, t) => n ^ " : " ^ type_to_string t) [("Encode", type_of ``Encode``), ("Decode", type_of ``Decode``), ("rd", type_of ``(ARB:word5)``), ("imm", type_of ``(ARB:word20)``)]) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
