Frame-occupancy probes for bead flapjack-pxn.8.5.14.1.3 (Cake IRC frame parity).
Each pair NAME.pnk + NAME.cake.S is a verbatim original-cake run:
  cat NAME.pnk | cake --pancake --target=riscv - > NAME.cake.S
Cake bitmap .quad words are 2^fprime per call continuation (word 0 = 4 header).

  p1  [4,2]          nothing live across call
  p2  [4,4]          scalar live across call
  p3  [4,4]          1-field struct, one read after call
  p4  [4,4]          1-field struct, same field read twice (CSE)
  p5  [4,4]          2-field struct, one read
  p6  [4,4,4]        struct from call, one read; shared ra slot
  p7  [4,4,4]        scalar from call live across second call
  p9  [4,8,8]        2-field struct, two distinct reads (separate ra slots)
  p10 [4,16,16]      3-field struct, three reads
  p11 [4,4,4]        2-field struct, same field twice (CSE)
  bm_min2      [4,8,8]        (bitmap-min) two distinct reads + t
  live1        [4,4,4]        one struct, one read
  live3        [4,16,16,16,16] three structs live across id call
  wide         [4,8,8]        6-field struct, first+last read
  bc           [4,2,2]        self-call recursion, trivial frame
  bitmap_calls [4,2,2]        same shape as bc
