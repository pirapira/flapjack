load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val ctx = ``([(«A», <| fields := [(«f», One)] ; size := 2n |>)] :
             (stcname # struct_info) list)``;

val _ = print_eval "ml_one_hit" ``mem_load One (0w:8 word) {(0w:8 word)} (\(_:8 word). Word (7w:8 word)) ([] : (stcname # struct_info) list)``;
val _ = print_eval "ml_one_miss" ``mem_load One (0w:8 word) ({} : 8 word set) (\(_:8 word). Word (7w:8 word)) ([] : (stcname # struct_info) list)``;
val _ = print_eval "ml_comb" ``mem_load (Comb [One; One]) (0w:8 word) {(0w:8 word); (1w:8 word)} (\(a:8 word). Word (n2w (w2n a + 1))) ([] : (stcname # struct_info) list)``;
val _ = print_eval "ml_named_hit" ``mem_load (Named «A») (0w:8 word) {(0w:8 word)} (\(_:8 word). Word (5w:8 word)) ^ctx``;
val _ = print_eval "ml_named_miss" ``mem_load (Named «Z») (0w:8 word) {(0w:8 word)} (\(_:8 word). Word (5w:8 word)) ^ctx``;
val _ = print_eval "ml_comb_offset" ``mem_load (Comb [One; One]) (0w:8 word) {(0w:8 word); (1w:8 word)} (\(a:8 word). Word (n2w (10 * w2n a))) ([] : (stcname # struct_info) list)``;