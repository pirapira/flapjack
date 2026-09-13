# RISC-V output format

This note documents the RISC-V artifact format produced by the original
Pancake compiler and the format the Flapjack port emits, so the two can be
compared directly without a conversion layer (bead `flapjack-pxn.8.5.11`).

## Original Pancake (`cake --pancake --target=riscv`)

The compiler prints a complete GNU assembler file.  The parts that matter for
byte comparison are:

1. A preprocessor macro block defining `cdecl`/`wcdecl`/`wcml`/`makesym`.
2. A `.data` section with the runtime `cml_heap`, `cml_stack`,
   `cml_stackend`, `cake_bitmaps` (`.quad 4`) and `cake_bitmaps_buffer_begin`
   / `cake_bitmaps_buffer_end` globals.
3. `.text` / `.p2align 3` and the C entry `cdecl(cml_main)` which loads
   `cake_main` and jumps to it.
4. The shared runtime stubs, named
   `cml__Init_0`, `cml__Halt0_1`, `cml__Halt2_2`, `cml__GC_3`,
   `cml__Raise_4`, `cml__StoreConsts_5`.
5. The label `cake_main:` followed by the whole code image as `.byte`
   lines: 16 bytes per line, uppercase hexadecimal, comma separated, one
   literal tab of indentation.
6. `cdecl(cake_codebuffer_begin)` / `.p2align 12` /
   `cdecl(cake_codebuffer_end)` / `.space 4096`.
7. A `makesym(name, base, len)` line per symbol.  `base` is the byte offset
   from `cake_main`; `len` is the byte length.  Generated symbols are
   `cml_generated_main_<N>` (the wrapper that runs global initializers) and
   `cml_<source-function>_<N>`, where `<N>` is the deterministic section
   number walking the code image.

## Flapjack (`flapjack-compile`, `--assembly`, or `--pancake`)

The port emits the same native assembly envelope for the code image it
actually produces:

```
.text
.p2align 3
cake_main:

	.byte 93,0E,80,03,...
	...
    makesym(cml_flapjack_runtime_0, 0, 76)
    makesym(cml_generated_main_1, 76, 4)
    makesym(cml_main_2, 80, 12)
```

* `.data`, startup, `cake_main`, and `cake_codebuffer_*` markers follow the
  native Pancake/CakeML framing. The port emits the supported runtime/image
  metadata directly; it does not synthesize an ELF file.
* `.byte` lines use the same 16-per-line, `0x`-prefixed uppercase,
  comma-separated layout.
* `makesym(name, base, len)` uses the same four-space indentation and the
  same `base`-relative-to-`cake_main` convention.
* Symbol naming policy:
  * section `0` is the port runtime/raise stub, named
    `cml_flapjack_runtime_0`;
  * section `1` is the injected entry wrapper that runs global initializers
    and tail-calls the renamed entry, named `cml_generated_main_1`;
  * section `L >= 2` is `cml_<name>_<L>`, where `<name>` is the source
    function name (a trailing prime from the entry rename is removed) in
    `List (CompiledFunction ...)` order.

`flapjack-compile --sections` prints the same sections in the raw form
`<label> <address> <bytes...>` for callers that do not need the frame.

## Comparison

`scripts/parity-bytes.py` parses both outputs with one shared parser
(`cake_main:` marker, `.byte` stream, `makesym` table) and compares the
reconstructed sections directly.  It normalizes only the deterministic
`cml_` prefix and trailing `_<N>` section number.

At the time of writing (integration head `d778e24`), all 87 original-Pancake
accepted programs in the 244-program corpus have at least one code section
whose bytes differ from Flapjack's (`programs=244 gaps=264`, no matches).
The remaining differences are tracked by:

* `flapjack-pxn.8.5.10.1` constant-return lowering;
* `flapjack-pxn.8.5.10.2` global-initializer generated entry;
* `flapjack-pxn.8.5.10.3` direct-call entry;
* `flapjack-pxn.8.5.11.1` symbol numbering and runtime/data framing.

## Known format/layout differences

* Symbol numbers start after the port's runtime/raise section rather than
  after CakeML's six runtime stubs; this deterministic numbering is preserved
  in the `makesym` names.
* The current port's runtime instruction set is not byte-identical to CakeML's
  shared `cml__Init_0` through `cml__StoreConsts_5` stubs; those code mismatches
  remain tracked separately from the now-matching artifact envelope.
* The generated instruction bytes differ (see the beads above).
