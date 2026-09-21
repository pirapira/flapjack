#!/usr/bin/env python3
"""Check the original-Cake allocator witnesses for exact RISC-V bytes.

These fixtures exercise distinct allocator/frame shapes: dead-raise
allocation, handler-frame continuation, a nested handler spill slot, colour
permutation, returned-value allocation, wide-call argument occupancy,
overflow-call frame slots, 64-bit
register pressure, SSA cutsets/parallel moves, loop copy-propagation state,
an indirect spilled-address carrier, five-word and nine-continuation frame
occupancy, a 22-slot ABI
call-frame, a whole-program 22-register parameter threshold, and a
stack-allocation boundary.  Keep the list explicit
so a change in the checked original-Cake witnesses is reviewable.
The expected Cake stdout hashes are pinned in ``parity-small-corpus.json``.
Comparing Flapjack's complete assembly stdout with those hashes keeps this
check exact while avoiding a dependency on the ignored/local Cake executable
in clean CI checkouts.
"""

import hashlib
import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
FLAPJACK = REPO_ROOT / ".lake" / "build" / "bin" / "flapjack-compile"
MANIFEST = REPO_ROOT / "scripts" / "parity-small-corpus.json"
FIXTURES = (
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00634_dead_raise.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f01266_raise_live_continuation.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00108_handler_spill_slot.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "allocator_frame_handler_min.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "gh1025_frame_bitmap.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "gh1025_frame_bitmap_f00000.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "allocator_colour_permutation.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00068_allocator_return.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00028_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "divmnu_copy_loop.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "bn_divmnu_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "mul64x64_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "wide_call_arguments.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "wide_call_arity.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "stack_args_overflow_slots.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "secp256k1_recover.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "many_word_parameters.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "gh1049_stack_alloc.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00014_loop_to_word_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "dec_temporary_cutset.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00068_throwminimal3.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00460_nested_handler_constant_fold.pnk",
)


def main() -> int:
    missing = [path for path in FIXTURES if not path.is_file()]
    if missing:
        for path in missing:
            print(f"missing allocator fixture: {path}", file=sys.stderr)
        return 2
    if not FLAPJACK.is_file():
        print(f"missing flapjack binary: {FLAPJACK}", file=sys.stderr)
        return 2
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    expected = {
        REPO_ROOT / fixture["path"]: fixture["cake_sha256"]
        for fixture in manifest["fixtures"]
    }
    failures = 0
    for path in FIXTURES:
        if path not in expected:
            print(f"missing pinned Cake hash: {path}", file=sys.stderr)
            failures += 1
            continue
        result = subprocess.run(
            [str(FLAPJACK), "--assembly", str(path)], capture_output=True
        )
        actual = hashlib.sha256(result.stdout).hexdigest()
        if result.returncode == 0 and actual == expected[path]:
            print(f"exact {path.name} sha256={actual}")
        else:
            print(
                f"MISMATCH {path.name} returncode={result.returncode} "
                f"cake={expected[path]} flapjack={actual}",
                file=sys.stderr,
            )
            failures += 1
    print(f"allocator fixtures={len(FIXTURES)} failures={failures}")
    return int(failures != 0)


if __name__ == "__main__":
    sys.exit(main())
