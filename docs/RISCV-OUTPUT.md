# RISC-V output format

This note documents the RISC-V artifact format produced by the original
Pancake compiler and the format the Flapjack port emits, so the two can be
compared directly without a conversion layer (beads `flapjack-pxn.8.5.11` and
`flapjack-pxn.8.5.11.4.1`).  The upstream reference used for the format
contract is the checked-in CakeML executable invoked as:

```
cake --pancake --target=riscv < SOURCE.pnk
```

The serializer regression checks in `Flapjack/Test/ArtifactFormat.lean` pin
the envelope markers, byte-line grouping/casing, and symbol-name conventions;
the direct corpus audit separately compares the emitted section payloads.

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

	.byte 0x13,0x65,0x70,0x00,...
	...
    makesym(cml__Init_0, 0, 756)
    makesym(cml__Halt0_1, 756, 8)
    makesym(cml__Halt2_2, 764, 8)
    makesym(cml__GC_3, 772, 40)
    makesym(cml__Raise_4, 812, 36)
    makesym(cml__StoreConsts_5, 848, 152)
    makesym(cml_generated_main_6, 1000, 4)
```

* `.data`, startup, `cake_main`, and `cake_codebuffer_*` markers follow the
  native Pancake/CakeML framing. The port emits the supported runtime/image
  metadata directly; it does not synthesize an ELF file.
* `.byte` lines use the same 16-per-line, `0x`-prefixed uppercase,
  comma-separated layout.
* `makesym(name, base, len)` uses the same four-space indentation and the
  same `base`-relative-to-`cake_main` convention.
* The supported RV64 runtime prefix is byte-equivalent to CakeML and occupies
  1000 bytes: Init 756, Halt0 8, Halt2 8, GC 40, Raise 36, and StoreConsts
  152. The generated entry wrapper therefore starts at offset 1000.
* Symbol naming follows Cake runtime numbering: cml__Init_0 through
  cml__StoreConsts_5, cml_generated_main_6, and cml_<name>_<N> for source
  functions.

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
* `flapjack-pxn.8.5.11.2` exact runtime section bytes, now covered by the
  fixed RV64 runtime prefix and its regression fixture; generated/user code
  mismatches remain tracked by the `.8.5.10.x` beads.

## Known format/layout differences

* The runtime prefix is fixed for the supported RV64 target and matches CakeML
  byte-for-byte. Remaining direct parity differences are in generated/user
  compiler code and are tracked separately.
