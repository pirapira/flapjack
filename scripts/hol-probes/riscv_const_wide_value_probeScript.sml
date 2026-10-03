load "preamble"; load "riscvTheory";
open HolKernel Parse bossLib preamble riscvTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
(* Literal wide Const branch value operations; ground evidence supplements the unrestricted kernel theorem. *)
fun out label tm = (print(label ^ "="); print_term(rhs(concl(EVAL tm))); print "\n");
fun replay label tm =
  (print (label ^ "="); print_term tm; print "\n");
val _ = out "const_wide_value_zero" ``let c = (0w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_low_positive_max" ``let c = (2147483647w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_low_sign_bit" ``let c = (2147483648w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_low_all_ones" ``let c = (4294967295w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_high_one" ``let c = (4294967296w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_high_one_low_sign" ``let c = (6442450944w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_positive_max" ``let c = (9223372036854775807w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_negative_min" ``let c = (9223372036854775808w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_negative_min_low_sign" ``let c = (9223372039002259456w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_negative_high_low_positive" ``let c = (18446744071562067967w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_negative_high_low_sign" ``let c = (18446744071562067968w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = out "const_wide_value_all_ones" ``let c = (18446744073709551615w : word64) in
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = (print "const_wide_value_source_clause="; print "HOL cakeml/compiler/encoders/riscv/riscv_targetScript.sml riscv_ast_def Const wide branches (l.104-114); value formula stated for arbitrary c, both branches."; print "\n");
val _ = replay "const_wide_value_replay" ``!(c:word64).
 (if c ' 31 then
   ((sw2sw (~((63 >< 32) c : word32)) : word64) << 32) ??
     (sw2sw ((31 >< 0) c : word32) : word64)
  else
   ((sw2sw ((63 >< 32) c : word32) : word64) << 32) ||
     (sw2sw ((31 >< 0) c : word32) : word64)) = c``;
val _ = print ("const_wide_value_carriers=" ^ String.concatWith ", " (map (fn (n, t) => n ^ " : " ^ type_to_string t) [("c", type_of ``(ARB:word64)``), ("result", type_of ``(ARB:word64)``)]) ^ "\n");
val _ = OS.Process.exit OS.Process.success;
