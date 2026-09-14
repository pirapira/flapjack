#!/bin/sh
# Replay nomain-global without the fuzzer.
set -e
cd /home/zksecurity/flapjack4
nice -n 10 timeout 20s /home/zksecurity/pancake-lean/cakeml/developers/bin/cake --pancake --target=riscv < scripts/parity-difffuzz-findings/nomain-global/case.pnk > cake.S 2> cake.err; echo cake exit=$?
nice -n 10 timeout 20s /home/zksecurity/flapjack4/.lake/build/bin/flapjack-compile --assembly /tmp/opencode/preserved/nomain-global.pnk > flapjack.S 2> flapjack.err; echo flapjack exit=$?
