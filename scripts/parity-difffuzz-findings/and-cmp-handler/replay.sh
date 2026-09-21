#!/bin/sh
# Replay the And-of-comparisons-in-handler parity witness.
CAKE=${CAKE:-/home/zksecurity/pancake-lean/cakeml/developers/bin/cake}
FLAPJACK=${FLAPJACK:-$(dirname "$0")/../../../.lake/build/bin/flapjack-compile}
DIR=$(dirname "$0")
"$CAKE" --pancake --target=riscv < "$DIR/case.pnk" > "$DIR/cake.S"
"$FLAPJACK" --assembly "$DIR/case.pnk" > "$DIR/flapjack.S"
echo "cake=$(wc -c < "$DIR/cake.S") flapjack=$(wc -c < "$DIR/flapjack.S")"
cmp "$DIR/cake.S" "$DIR/flapjack.S" && echo SAME || echo DIFF
