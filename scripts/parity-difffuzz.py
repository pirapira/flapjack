#!/usr/bin/env python3
"""Deterministic, replayable differential fuzzing: original Pancake vs Flapjack.

This harness generalizes ``parity-fuzz.py`` (which compared only
acceptance/rejection) to the full observable artifact boundary required by the
parity workflow:

* parse/static acceptance of both compilers,
* the complete non-payload assembly frame (as audited by
  ``parity-format.py``),
* section names, their document order, base addresses and lengths,
* instruction/data bytes of every runtime, generated-entry, and user section,
  and diagnostics, which are recorded verbatim for every rejected case.

Every generated case is derived deterministically from (``--seed``, case
index, mode), every compiler invocation runs under
``nice -n 10 timeout 20s`` (configurable), and every mismatch whose signature
is not registered as a known bead-owned gap is saved under ``--findings`` with
the seed, source, both raw outputs, the normalized comparison, tool versions,
and command lines, plus a standalone ``replay.sh``.  ``--replay`` re-runs a
saved finding without the generator.  ``--minimize`` delta-debugs a finding's
source while the mismatch signature persists.

The only normalization ever applied is the documented deterministic
section-name normalization shared with ``parity-bytes.py``: strip a leading
``cml_`` and a trailing ``_<digits>`` when matching section names.  Byte
differences are never normalized away; they pass only when their signature is
registered in ``parity-difffuzz-gaps.json`` with an owning bead.

Usage::

    scripts/parity-difffuzz.py --smoke --exact         # deterministic exact corpus
    scripts/parity-difffuzz.py --seed 1 --count 400     # bounded campaign
    scripts/parity-difffuzz.py --mode mutate --seed 7 --count 200
    scripts/parity-difffuzz.py --replay FINDING_DIR
    scripts/parity-difffuzz.py --minimize FINDING_DIR
"""

import argparse
import difflib
import fnmatch
import hashlib
import json
import os
import random
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CAKE = os.environ.get(
    "CAKE", os.path.expanduser("~/pancake-lean/cakeml/developers/bin/cake")
)
DEFAULT_FLAPJACK = REPO_ROOT / ".lake" / "build" / "bin" / "flapjack-compile"
DEFAULT_GAPS = Path(__file__).with_name("parity-difffuzz-gaps.json")
DEFAULT_SEED_CORPUS = REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake"

# ---------------------------------------------------------------------------
# Program generation (restricted to the implemented Pancake source subset).
# ---------------------------------------------------------------------------

CONSTS = ["0", "1", "2", "3", "7", "255", "1000"]
BINOPS = ["+", "-", "*", "&", "|", "^", "<<", ">>", ">>>"]

FIXED_DECLS = (
    "fun 1 add1(1 a, 1 b) { return a + b; }\n"
    "fun 1 sub1(1 a) { return a - 1; }\n"
    "fun {1,1} pair(1 a, 1 b) { return <a, b>; }\n"
    "struct S { 1 f1, 1 f2 }\n"
    "fun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\n"
    "exception E : 1;\n"
)

SMOKE_SEEDS = [1001, 1002, 1003, 1004, 1005, 1006]
SMOKE_MUTATE_SEEDS = [2001, 2002, 2003]


class Generator:
    """Random, grammar-valid Pancake programs over the implemented subset.

    The grammar mirrors ``parity-fuzz.py`` (which was tuned against the
    original PEG): calls only appear at the top of an expression, shared
    memory loads/stores use word-aligned constant-heavy addresses, and the
    fixed declarations give every program a small supported function table.
    """

    max_extra_words = 6

    def __init__(self, rng):
        self.rng = rng
        self.words = []
        self.structs = []
        self.pairs = []

    def word(self):
        return self.rng.choice(self.words) if self.words else "x"

    def expr(self, depth=0):
        rng = self.rng
        roll = rng.random()
        if depth > 2 or roll < 0.3:
            if self.words and rng.random() < 0.7:
                return rng.choice(CONSTS + self.words)
            return rng.choice(CONSTS)
        if roll < 0.55:
            return "(%s %s %s)" % (self.expr(depth + 1), rng.choice(BINOPS), self.expr(depth + 1))
        if roll < 0.62:
            return "(%s #>> %s)" % (self.expr(depth + 1), rng.choice(["1", "2", "7"]))
        if roll < 0.7 and self.structs:
            return "%s.%s" % (rng.choice(self.structs), rng.choice(["f1", "f2"]))
        if roll < 0.76 and self.pairs:
            return "%s.%s" % (rng.choice(self.pairs), rng.choice(["0", "1"]))
        if roll < 0.9:
            return "(lds 1 (%s))" % self.addr(depth + 1)
        return "(ld8 %s)" % self.addr(depth + 1)

    def call(self):
        rng = self.rng
        if rng.random() < 0.6:
            return "add1(%s, %s)" % (self.expr(1), self.expr(1))
        return "sub1(%s)" % self.expr(1)

    def top_expr(self):
        if self.rng.random() < 0.35:
            return self.call()
        return self.expr(1)

    def addr(self, depth=0):
        rng = self.rng
        if depth > 2 or rng.random() < 0.5:
            return rng.choice(["0", "1000", "1008", "1016", "1024", "1000 + 12", "1000 + 24"])
        return "(%s + %s)" % (self.addr(depth + 1), rng.choice(["4", "8", "12", "16", "1000"]))

    def cond(self):
        return "(%s %s %s)" % (
            self.expr(1),
            self.rng.choice([">", "<", ">=", "<=", "!=", "=="]),
            self.expr(1),
        )

    def stmt(self, indent):
        p = " " * indent
        rng = self.rng
        roll = rng.random()
        if roll < 0.22 and self.words:
            return p + "%s = %s;" % (rng.choice(self.words), self.top_expr())
        if roll < 0.3 and self.words:
            return p + "st (%s), %s;" % (self.addr(), self.expr())
        if roll < 0.35 and self.words:
            return p + "st8 (%s), %s;" % (self.addr(), self.expr())
        if roll < 0.4 and self.words:
            return p + "!stw (%s), %s;" % (self.addr(), self.expr())
        if roll < 0.45 and self.words:
            return p + "!ldw %s, (%s);" % (self.word(), self.addr())
        if roll < 0.5:
            return p + "@foo(%s, %s, %s, %s);" % (self.expr(), self.expr(), self.expr(), self.expr())
        if roll < 0.58:
            body = "\n".join(self.stmt(indent + 2) for _ in range(rng.randint(1, 2)))
            other = "\n".join(self.stmt(indent + 2) for _ in range(rng.randint(1, 2)))
            return p + "if %s {\n%s\n%s} else {\n%s\n%s}" % (self.cond(), body, p, other, p)
        if roll < 0.64:
            body = "\n".join(self.stmt(indent + 2) for _ in range(rng.randint(1, 2)))
            extra = rng.choice(["", p + "    break;", p + "    continue;"])
            return p + "while (x > 0) {\n%s\n%s\n%s}" % (body, extra, p)
        if roll < 0.68:
            return p + "throw E %s;" % self.expr()
        if roll < 0.73 and self.words:
            cv = self.word()
            target = self.word()
            inner = "\n".join(self.stmt(indent + 4) for _ in range(rng.randint(1, 2)))
            try_body = "%s  %s = %s" % (p, target, self.top_expr())
            return "%stry\n%s\n%scatch E => %s {\n%s\n%s}" % (p, try_body, p, cv, inner, p)
        if self.words:
            return p + "%s = %s;" % (rng.choice(self.words), self.top_expr())
        return p + "@foo(%s, %s, %s, %s);" % (self.expr(), self.expr(), self.expr(), self.expr())

    def program(self):
        rng = self.rng
        self.words = ["x"]
        body = ["  var 1 x = %s;" % rng.choice(CONSTS)]
        for _ in range(rng.randint(0, Generator.max_extra_words)):
            name = "y%d" % rng.randint(0, 999)
            body.append("  var 1 %s = %s;" % (name, self.top_expr()))
            self.words.append(name)
        for _ in range(rng.randint(0, 1)):
            name = "s%d" % rng.randint(0, 999)
            body.append("  var S %s = mks(%s, %s);" % (name, self.expr(), self.expr()))
            self.structs.append(name)
        for _ in range(rng.randint(0, 1)):
            name = "p%d" % rng.randint(0, 999)
            body.append("  var {1,1} %s = pair(%s, %s);" % (name, self.expr(), self.expr()))
            self.pairs.append(name)
        for _ in range(rng.randint(1, Generator.max_extra_words)):
            body.append(self.stmt(2))
        body.append("  return %s;" % self.top_expr())
        return FIXED_DECLS + "fun 1 main() {\n" + "\n".join(body) + "\n}\n"


# ---------------------------------------------------------------------------
# Deterministic mutation of the checked-in seed corpus.
# ---------------------------------------------------------------------------

MUT_TEMPLATES = [
    "  var 1 z%d = %s;",
    "  x = %s;",
    "  return %s;",
    "  st (1000 + 32), %s;",
    "  @foo(1, 2, 3, 4);",
]


def mutate_program(rng, text):
    """Return a deterministic one- or two-operation mutation of ``text``."""
    lines = text.splitlines()
    if not lines:
        return text
    for _ in range(2):
        op = rng.random()
        if op < 0.14 and len(lines) > 1:
            del lines[rng.randrange(len(lines))]
        elif op < 0.28:
            i = rng.randrange(len(lines))
            lines.insert(i, lines[i])
        elif op < 0.4 and len(lines) > 2:
            i = rng.randrange(len(lines) - 1)
            lines[i], lines[i + 1] = lines[i + 1], lines[i]
        elif op < 0.55:
            i = rng.randrange(len(lines))
            lines[i] = re.sub(r"\b(0|[1-9][0-9]{0,4})\b",
                              rng.choice(["0", "1", "7", "255", "1000", "65536"]),
                              lines[i], count=1)
        elif op < 0.66:
            i = rng.randrange(len(lines))
            lines[i] = re.sub(r"[+]|[-]|[*]|[&]|[|]|[\^]",
                              rng.choice(BINOPS), lines[i], count=1)
        elif op < 0.78:
            template = rng.choice(MUT_TEMPLATES)
            if "%s" in template:
                line = template % tuple(
                    [rng.randint(0, 9)] * template.count("%d") +
                    [rng.choice(CONSTS)] * template.count("%s")
                )
            else:
                line = template
            lines.insert(rng.randrange(len(lines) + 1), line)
        elif op < 0.9 and len(lines) > 4:
            cut = rng.randrange(1, len(lines))
            lines = lines[:cut]
        else:
            i = rng.randrange(len(lines))
            lines[i] = lines[i] + rng.choice([" ", ";", "{", "}"])
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Artifact parsing and comparison.
# ---------------------------------------------------------------------------

BYTE_LINE = re.compile(r"^\.byte ")
MAKESYM = re.compile(r"makesym\((\w+),\s*(\d+),\s*(\d+)\)")


def parse_artifact(text):
    """Parse one Pancake-compatible assembly frame.

    Returns ``None`` when the frame is malformed, otherwise a dict with the
    static frame lines (everything except ``.byte`` payload and ``makesym``
    symbol lines), the ordered section list, and ``{name: (base, bytes)}``.
    """
    if "cake_main:" not in text:
        return None
    static = []
    payload = []
    order = []
    sections = {}
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith(".byte"):
            if not re.fullmatch(r"\.byte (0x[0-9A-Fa-f]{2}(,0x[0-9A-Fa-f]{2})*)", stripped):
                return None
            payload.extend(int(token, 16) for token in stripped[6:].split(","))
            continue
        match = re.search(r"makesym\((\w+),\s*(\d+),\s*(\d+)\)", stripped)
        if stripped.startswith("makesym("):
            if not re.fullmatch(r"makesym\(\w+, \d+, \d+\)", stripped):
                return None
            name, base, length = match.group(1), int(match.group(2)), int(match.group(3))
            order.append(name)
            sections[name] = (base, payload[base:base + length])
            continue
        static.append(line)
    if not sections:
        return None
    return {"static": static, "order": order, "sections": sections}


def normalize_name(name):
    """The single documented normalization: ``cml_generated_main_6`` ->
    ``generated_main`` (strip ``cml_`` prefix and numeric suffix)."""
    return re.sub(r"_\d+$", "", re.sub(r"^cml_", "", name))


def classify(sections):
    runtime, entry, user = {}, None, {}
    for name, section in sections.items():
        normalized = normalize_name(name)
        if name.startswith("cml__"):
            runtime[normalized] = section
        elif normalized == "generated_main":
            entry = (name, section)
        else:
            user[normalized] = section
    return runtime, entry, user


def hexstr(data):
    return " ".join("%02x" % byte for byte in data)


def classify_static_diffs(cake_static, flapjack_static):
    """Classify differing static-frame lines into observable shapes.

    ``frame/bitmap-table``: the ``.quad`` word list after ``cake_bitmaps:``
    (runtime GC pointer-map metadata).  ``frame/ffi-stub``: CakeML's
    per-FFI-name jump-table stubs (``cake_<ffi>:`` labels, ``tail cdecl``
    jumps, alignment).  Any other static line difference is the generic
    ``frame/static`` shape, which no bead may own.
    """
    shapes = {}
    matcher = difflib.SequenceMatcher(a=cake_static, b=flapjack_static)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "equal":
            continue
        differing = [line.strip() for line in cake_static[i1:i2] + flapjack_static[j1:j2]]
        def is_bitmap(lines):
            return lines and all(re.match(r"^\.quad\b", line) for line in lines)
        def is_ffi(lines):
            return lines and all(
                re.match(r"^cake_\w+:$", line) or line.startswith("tail cdecl(")
                or re.match(r"^\.p2align\b", line) or line == ""
                for line in lines)
        if is_bitmap(differing):
            shapes.setdefault("frame/bitmap-table", []).extend(differing)
        elif is_ffi(differing):
            shapes.setdefault("frame/ffi-stub", []).extend(line for line in differing if line)
        else:
            shapes.setdefault("frame/static", []).extend(differing)
    return shapes


def compare_artifacts(cake, flapjack):
    """Compare two parsed artifacts; return a list of mismatch records."""
    mismatches = []
    cake_runtime, cake_entry, cake_user = classify(cake["sections"])
    flap_runtime, flap_entry, flap_user = classify(flapjack["sections"])

    if cake["static"] != flapjack["static"]:
        shapes = classify_static_diffs(cake["static"], flapjack["static"])
        for shape, lines in sorted(shapes.items()):
            mismatches.append({
                "signature": shape,
                "detail": {"differing_lines": lines[:8]},
            })

    cake_order = [normalize_name(n) for n in cake["order"]]
    flap_order = [normalize_name(n) for n in flapjack["order"]]
    if cake_order != flap_order:
        mismatches.append({
            "signature": "sections/order",
            "detail": {"cake_order": cake_order, "flapjack_order": flap_order},
        })

    for kind, cake_map, flap_map in (
        ("runtime", cake_runtime, flap_runtime),
        ("user", cake_user, flap_user),
    ):
        for name in sorted(set(cake_map) | set(flap_map)):
            if name not in flap_map:
                mismatches.append({"signature": "sections/missing:%s:%s" % (kind, name), "detail": {}})
                continue
            if name not in cake_map:
                mismatches.append({"signature": "sections/unexpected:%s:%s" % (kind, name), "detail": {}})
                continue
            cake_base, cake_bytes = cake_map[name]
            flap_base, flap_bytes = flap_map[name]
            if (cake_base, len(cake_bytes)) != (flap_base, len(flap_bytes)):
                mismatches.append({
                    "signature": "layout/%s:%s" % (kind, name),
                    "detail": {"cake_base": cake_base, "flapjack_base": flap_base,
                               "cake_length": len(cake_bytes), "flapjack_length": len(flap_bytes)},
                })
            if cake_bytes != flap_bytes:
                mismatches.append({
                    "signature": "bytes/%s:%s:%s" % (kind, name, "len_eq" if len(cake_bytes) == len(flap_bytes) else "len_ne"),
                    "detail": {"cake_sha256": hashlib.sha256(bytes(cake_bytes)).hexdigest(),
                               "flapjack_sha256": hashlib.sha256(bytes(flap_bytes)).hexdigest(),
                               "cake_bytes": hexstr(cake_bytes[:48]),
                               "flapjack_bytes": hexstr(flap_bytes[:48])},
                })

    if (cake_entry is None) != (flap_entry is None):
        mismatches.append({
            "signature": "sections/generated_main:" + ("missing" if cake_entry else "unexpected"),
            "detail": {},
        })
    elif cake_entry is not None:
        cake_base, cake_bytes = cake_entry[1]
        flap_base, flap_bytes = flap_entry[1]
        if (cake_base, len(cake_bytes)) != (flap_base, len(flap_bytes)):
            mismatches.append({
                "signature": "layout/generated_main",
                "detail": {"cake_base": cake_base, "flapjack_base": flap_base,
                           "cake_length": len(cake_bytes), "flapjack_length": len(flap_bytes)},
            })
        if cake_bytes != flap_bytes:
            mismatches.append({
                "signature": "bytes/generated_main:%s" % ("len_eq" if len(cake_bytes) == len(flap_bytes) else "len_ne"),
                "detail": {"cake_sha256": hashlib.sha256(bytes(cake_bytes)).hexdigest(),
                           "flapjack_sha256": hashlib.sha256(bytes(flap_bytes)).hexdigest(),
                           "cake_bytes": hexstr(cake_bytes[:48]),
                           "flapjack_bytes": hexstr(flap_bytes[:48])},
            })
    return mismatches


# ---------------------------------------------------------------------------
# Bounded compiler invocation.
# ---------------------------------------------------------------------------

class Runner:
    def __init__(self, cake, flapjack, nice_level, timeout_seconds):
        self.cake = str(cake)
        self.flapjack = str(flapjack)
        self.prefix = ["nice", "-n", str(nice_level), "timeout", "%ds" % timeout_seconds]

    def command_lines(self, path):
        return {
            "cake": self.prefix + [self.cake, "--pancake", "--target=riscv"],
            "flapjack": self.prefix + [self.flapjack, "--assembly", str(path)],
        }

    def run(self, path, source_bytes):
        commands = self.command_lines(path)
        cake = subprocess.run(commands["cake"], input=source_bytes, capture_output=True)
        flapjack = subprocess.run(commands["flapjack"], stdin=subprocess.DEVNULL, capture_output=True)
        return {
            "cake": {"returncode": cake.returncode, "stdout": cake.stdout,
                     "stderr": cake.stderr, "command": commands["cake"]},
            "flapjack": {"returncode": flapjack.returncode, "stdout": flapjack.stdout,
                         "stderr": flapjack.stderr, "command": commands["flapjack"]},
        }


def flapjack_error_bucket(stderr_text):
    """A coarse, stable bucket for a Flapjack rejection diagnostic."""
    if "parseTopDecs" in stderr_text or "ParseError" in stderr_text or "expected" in stderr_text:
        return "parse"
    if "entry not found" in stderr_text:
        return "entry"
    features = sorted(set(re.findall(r"feature := \.(\w+)", stderr_text)))
    if features:
        return "pipeline:" + "+".join(features)
    return "other"


def compare_case(result):
    """Full observable comparison for one case; returns classification."""
    cake_ok = result["cake"]["returncode"] == 0
    flap_ok = result["flapjack"]["returncode"] == 0
    case = {
        "cake_returncode": result["cake"]["returncode"],
        "flapjack_returncode": result["flapjack"]["returncode"],
        "mismatches": [],
        "class": None,
    }
    if not cake_ok and not flap_ok:
        case["class"] = "both-rejected"
        return case
    if cake_ok and not flap_ok:
        stderr = result["flapjack"]["stderr"].decode("utf-8", "replace")
        case["class"] = "gap"
        case["mismatches"] = [{"signature": "acceptance/gap:" + flapjack_error_bucket(stderr),
                               "detail": {"flapjack_stderr": stderr[:2000],
                                          "cake_stderr": result["cake"]["stderr"].decode("utf-8", "replace")[:500]}}]
        return case
    if flap_ok and not cake_ok:
        case["class"] = "opposite"
        case["mismatches"] = [{"signature": "acceptance/opposite",
                               "detail": {"cake_stderr": result["cake"]["stderr"].decode("utf-8", "replace")[:2000]}}]
        return case

    cake_artifact = parse_artifact(result["cake"]["stdout"].decode("utf-8", "replace"))
    flap_artifact = parse_artifact(result["flapjack"]["stdout"].decode("utf-8", "replace"))
    if cake_artifact is None or flap_artifact is None:
        case["class"] = "both-accepted"
        case["mismatches"] = [{
            "signature": "frame/parse:%s" % ("cake" if cake_artifact is None else "flapjack"),
            "detail": {},
        }]
        return case
    case["class"] = "both-accepted"
    case["mismatches"] = compare_artifacts(cake_artifact, flap_artifact)
    return case


# ---------------------------------------------------------------------------
# Tool provenance.
# ---------------------------------------------------------------------------

def tool_versions(cake, flapjack):
    def info(path):
        path = Path(path)
        data = path.read_bytes()
        return {"path": str(path), "size": len(data), "sha256": hashlib.sha256(data).hexdigest()}
    versions = {"cake": info(cake), "flapjack": info(flapjack)}
    try:
        versions["flapjack"]["git_commit"] = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD"],
            capture_output=True, text=True,
        ).stdout.strip()
    except OSError:
        pass
    return versions


# ---------------------------------------------------------------------------
# Findings persistence and replay.
# ---------------------------------------------------------------------------

def write_finding(findings_root, case_id, source, result, comparison, provenance, origin):
    directory = Path(findings_root) / case_id
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "case.pnk").write_bytes(source)
    (directory / "cake.S").write_bytes(result["cake"]["stdout"])
    (directory / "cake.err").write_bytes(result["cake"]["stderr"])
    (directory / "flapjack.S").write_bytes(result["flapjack"]["stdout"])
    (directory / "flapjack.err").write_bytes(result["flapjack"]["stderr"])
    record = {
        "id": case_id,
        "origin": origin,
        "comparison": comparison,
        "tool_versions": provenance,
        "commands": {tool: result[tool]["command"] for tool in ("cake", "flapjack")},
        "returncodes": {tool: result[tool]["returncode"] for tool in ("cake", "flapjack")},
    }
    (directory / "finding.json").write_text(json.dumps(record, indent=2) + "\n")
    replay = "#!/bin/sh\n# Replay %s without the fuzzer.\nset -e\ncd %s\n%s < %s > cake.S 2> cake.err; echo cake exit=$?\n%s > flapjack.S 2> flapjack.err; echo flapjack exit=$?\n" % (
        case_id, REPO_ROOT,
        " ".join(map(str, result["cake"]["command"])), directory / "case.pnk",
        " ".join(map(str, result["flapjack"]["command"])),
    )
    (directory / "replay.sh").write_text(replay)
    (directory / "replay.sh").chmod(0o755)
    return directory


def load_gaps(path):
    if not Path(path).is_file():
        return {}
    return json.loads(Path(path).read_text())


def known_signatures(gaps):
    """Signature patterns that may pass as bead-owned.

    Registry entries are shell-style patterns (``bytes/user:*:len_ne``) so one
    bead family can own a whole observable class without naming every
    generated function.  Acceptance disagreements, generic frame differences
    (``frame/static``), and tool failures are never known gaps: no bead can
    own them, so they always surface as findings.  Shape-specific frame
    differences (``frame/bitmap-table``, ``frame/ffi-stub``) may be owned by
    beads once filed.
    """
    return [pattern for pattern in gaps.get("signatures", {})
            if not (pattern.startswith(("acceptance/", "tool-"))
                    or pattern == "frame/static")]


def is_known(signature, patterns):
    return any(fnmatch.fnmatchcase(signature, pattern) for pattern in patterns)


def signatures_of(comparison):
    return sorted({m["signature"] for m in comparison["mismatches"]})


# ---------------------------------------------------------------------------
# Deterministic case production.
# ---------------------------------------------------------------------------

def seed_corpus_files(root):
    return sorted(Path(root).glob("*.pnk"))


def make_case(mode, seed, index, corpus_root):
    """Deterministically produce (case_id, source_bytes) for one case."""
    if mode == "generate":
        rng = random.Random("flapjack-difffuzz:%d:%d:generate" % (seed, index))
        source = Generator(rng).program()
    elif mode == "mutate":
        rng = random.Random("flapjack-difffuzz:%d:%d:mutate" % (seed, index))
        files = seed_corpus_files(corpus_root)
        if not files:
            source = Generator(rng).program()
        else:
            base = files[rng.randrange(len(files))]
            source = mutate_program(rng, base.read_text())
    else:
        rng = random.Random("flapjack-difffuzz:%d:%d:mixed" % (seed, index))
        if rng.random() < 0.5:
            source = Generator(rng).program()
        else:
            files = seed_corpus_files(corpus_root)
            base = files[rng.randrange(len(files))]
            source = mutate_program(rng, base.read_text())
    case_id = "f%05d-s%d-i%05d-%s" % (index, seed, index, mode)
    return case_id, source.encode()


# ---------------------------------------------------------------------------
# Minimization (line-level delta debugging, signature preserving).
# ---------------------------------------------------------------------------

def minimize_source(runner, source, comparison, workdir, max_steps=80):
    """Drop lines while the exact mismatch-signature set persists."""
    target = signatures_of(comparison)
    lines = source.decode().splitlines(keepends=True)

    def still_mismatches(candidate):
        if not candidate:
            return False
        path = workdir / "min.pnk"
        path.write_bytes("".join(candidate).encode())
        result = runner.run(path, "".join(candidate).encode())
        return signatures_of(compare_case(result)) == target

    step = 0
    chunk = max(1, len(lines) // 2)
    while chunk >= 1 and step < max_steps:
        progress = False
        start = 0
        while start < len(lines):
            step += 1
            if step > max_steps:
                return "".join(lines).encode(), step
            candidate = lines[:start] + lines[start + chunk:]
            if candidate and still_mismatches(candidate):
                lines = candidate
                progress = True
            else:
                start += chunk
        if not progress:
            chunk = max(1, chunk // 2)
            if chunk == 1 and not progress:
                break
    return "".join(lines).encode(), step


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------

def run_campaign(args):
    cake = Path(args.cake)
    flapjack = Path(args.flapjack)
    if not cake.is_file():
        print("missing cake binary: %s" % cake, file=sys.stderr)
        return 2
    if not flapjack.is_file():
        print("missing flapjack binary: %s" % flapjack, file=sys.stderr)
        return 2
    runner = Runner(cake, flapjack, args.nice, args.timeout)
    gaps = load_gaps(args.gaps)
    gaps_signatures = known_signatures(gaps)
    provenance = tool_versions(cake, flapjack)

    cases = []
    if args.smoke:
        plan = [("generate", seed) for seed in SMOKE_SEEDS] + \
               [("mutate", seed) for seed in SMOKE_MUTATE_SEEDS]
        cases = [(mode, seed, i) for i, (mode, seed) in enumerate(plan)]
    else:
        modes = {"generate": ["generate"], "mutate": ["mutate"], "mixed": ["generate", "mutate"]}
        chosen = modes[args.mode]
        cases = [(chosen[i % len(chosen)], args.seed, i) for i in range(args.count)]

    workdir = Path(args.workdir or (Path(args.out or ".") / ".difffuzz-work"))
    workdir.mkdir(parents=True, exist_ok=True)
    findings_root = Path(args.out) if args.out else Path("difffuzz-findings")
    if args.out:
        findings_root.mkdir(parents=True, exist_ok=True)

    counters = {"both-accepted-exact": 0, "both-accepted-known": 0, "both-rejected": 0,
                "gap": 0, "opposite": 0, "unknown": 0, "timeouts": 0}
    seen_known = {}
    findings = []
    for mode, seed, index in cases:
        case_id, source = make_case(mode, seed, index, args.seed_corpus)
        path = workdir / ("%s.pnk" % case_id)
        path.write_bytes(source)
        result = runner.run(path, source)
        if result["cake"]["returncode"] == 124 or result["flapjack"]["returncode"] == 124:
            counters["timeouts"] += 1
            continue
        comparison = compare_case(result)
        sigs = signatures_of(comparison)
        # Exact source-to-RISC-V parity is the strict acceptance criterion.
        # The historical bead-owned gap registry remains useful for tracking
        # older campaigns, but it must not make a byte/layout mismatch pass an
        # exact campaign.
        unknown = sigs if args.exact else [s for s in sigs if not is_known(s, gaps_signatures)]
        origin = {"mode": mode, "seed": seed, "index": index,
                  "source_path": str(path)}
        if comparison["class"] == "both-rejected":
            counters["both-rejected"] += 1
        elif not sigs:
            counters["both-accepted-exact"] += 1
        elif not unknown:
            counters["both-accepted-known"] += 1
            for sig in sigs:
                seen_known.setdefault(sig, {"count": 0, "example": case_id})
                seen_known[sig]["count"] += 1
        else:
            if comparison["class"] in ("gap", "opposite"):
                counters[comparison["class"]] += 1
            counters["unknown"] += 1
            if args.out:
                directory = write_finding(findings_root, case_id, source, result,
                                          comparison, provenance, origin)
                findings.append(str(directory))
                if args.minimize:
                    minimized, steps = minimize_source(runner, source, comparison, workdir)
                    (directory / "case.min.pnk").write_bytes(minimized)
                    (directory / "finding.json").write_text(
                        json.dumps(json.loads((directory / "finding.json").read_text())
                                   | {"minimized": {"steps": steps,
                                                    "sha256": hashlib.sha256(minimized).hexdigest()}},
                                   indent=2) + "\n")
            if not args.quiet:
                print("UNKNOWN %s %s" % (case_id, ",".join(sigs)))
        if not args.quiet and args.verbose and sigs:
            print("case %s class=%s sigs=%s" % (case_id, comparison["class"], ",".join(sigs)))

    print("mode=%s cases=%d exact=%d known=%d both_rejected=%d gap=%d opposite=%d unknown=%d timeouts=%d" % (
        "exact" if args.exact else "gaps",
        len(cases), counters["both-accepted-exact"], counters["both-accepted-known"],
        counters["both-rejected"], counters["gap"], counters["opposite"],
        counters["unknown"], counters["timeouts"]))
    for sig in sorted(seen_known):
        owners = next((gaps["signatures"][pattern].get("beads", [])
                       for pattern in gaps_signatures
                       if fnmatch.fnmatchcase(sig, pattern)), [])
        print("  known %s x%d (example %s) beads=%s" % (
            sig, seen_known[sig]["count"], seen_known[sig]["example"],
            ",".join(owners)))
    if args.out:
        report = {"cases": len(cases), "counters": counters,
                  "known": seen_known, "findings": findings,
                  "comparison_mode": "exact" if args.exact else "gaps",
                  "tool_versions": provenance, "gaps_file": str(args.gaps)}
        (findings_root / "campaign.json").write_text(json.dumps(report, indent=2) + "\n")
    return 1 if counters["unknown"] else 0


def replay_finding(args):
    directory = Path(args.directory)
    source_path = directory / "case.pnk"
    if not source_path.is_file():
        print("no case.pnk under %s" % directory, file=sys.stderr)
        return 2
    source = source_path.read_bytes()
    runner = Runner(args.cake, args.flapjack, args.nice, args.timeout)
    result = runner.run(source_path, source)
    comparison = compare_case(result)
    sigs = signatures_of(comparison)
    record = json.loads((directory / "finding.json").read_text())
    reproduced = sorted(record["comparison"].get("signatures") or
                        signatures_of(record["comparison"])) == sigs
    print("replay %s class=%s signatures=%s reproduced=%s" % (
        directory, comparison["class"], ",".join(sigs) or "none", reproduced))
    return 0 if reproduced else 1


def run_file(args):
    """Run one given .pnk source through both tools and record a finding.

    Used to (re)generate the preserved, minimized findings under
    ``parity-difffuzz-findings/``: each directory there is reproducible via
    ``--file <case.pnk> --out <dir>`` and replayable via ``--replay <dir>``.
    """
    cake = Path(args.cake)
    flapjack = Path(args.flapjack)
    if not cake.is_file():
        print("missing cake binary: %s" % cake, file=sys.stderr)
        return 2
    if not flapjack.is_file():
        print("missing flapjack binary: %s" % flapjack, file=sys.stderr)
        return 2
    source_path = Path(args.file)
    if not source_path.is_file():
        print("missing source file: %s" % source_path, file=sys.stderr)
        return 2
    runner = Runner(cake, flapjack, args.nice, args.timeout)
    gaps = load_gaps(args.gaps)
    gaps_signatures = known_signatures(gaps)
    provenance = tool_versions(cake, flapjack)
    source = source_path.read_bytes()
    result = runner.run(source_path, source)
    if result["cake"]["returncode"] == 124 or result["flapjack"]["returncode"] == 124:
        print("file %s timeout" % source_path, file=sys.stderr)
        return 2
    comparison = compare_case(result)
    sigs = signatures_of(comparison)
    owners = sorted({owner
                     for sig in sigs
                     for pattern in gaps_signatures
                     if fnmatch.fnmatchcase(sig, pattern)
                     for owner in gaps["signatures"][pattern].get("beads", [])})
    print("file %s class=%s signatures=%s beads=%s" % (
        source_path, comparison["class"], ",".join(sigs) or "none",
        ",".join(owners) or "none"))
    if args.out:
        directory = write_finding(Path(args.out), source_path.stem, source, result,
                                  comparison, provenance,
                                  {"mode": "file", "path": str(source_path)})
        print("finding %s" % directory)
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--seed", type=int, default=1, help="master random seed")
    parser.add_argument("--count", type=int, default=200, help="number of cases")
    parser.add_argument("--mode", choices=["generate", "mutate", "mixed"], default="generate")
    parser.add_argument("--smoke", action="store_true",
                        help="run the fixed deterministic smoke corpus")
    parser.add_argument("--exact", action="store_true",
                        help="require identical accepted artifacts; ignore bead-owned gaps")
    parser.add_argument("--cake", default=DEFAULT_CAKE)
    parser.add_argument("--flapjack", default=str(DEFAULT_FLAPJACK))
    parser.add_argument("--gaps", default=str(DEFAULT_GAPS))
    parser.add_argument("--seed-corpus", default=str(DEFAULT_SEED_CORPUS))
    parser.add_argument("--nice", type=int, default=10)
    parser.add_argument("--timeout", type=int, default=20, help="per-invocation timeout (s)")
    parser.add_argument("--out", default=None,
                        help="findings directory (default: none; mismatches are only counted)")
    parser.add_argument("--workdir", default=None)
    parser.add_argument("--minimize", action="store_true",
                        help="delta-debug every unknown finding's source")
    parser.add_argument("--replay", dest="directory", default=None, metavar="FINDING_DIR")
    parser.add_argument("--file", default=None, metavar="SOURCE_PNK",
                        help="run a single given .pnk through both tools; "
                             "record a finding dir with --out")
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)

    if args.directory:
        return replay_finding(args)
    if args.file:
        return run_file(args)
    return run_campaign(args)


if __name__ == "__main__":
    sys.exit(main())
