#!/bin/sh
# Replay ffi-min without the fuzzer.
set -e
cd /home/zksecurity/flapjack4
nice -n 10 timeout 20s /home/zksecurity/pancake-lean/cakeml/developers/bin/cake --pancake --target=riscv < scripts/parity-difffuzz-findings/ffi-min/case.pnk > cake.S 2> cake.err; echo cake exit=$?
nice -n 10 timeout 20s /home/zksecurity/flapjack4/.lake/build/bin/flapjack-compile --assembly /tmp/opencode/preserved/ffi-min.pnk > flapjack.S 2> flapjack.err; echo flapjack exit=$?
