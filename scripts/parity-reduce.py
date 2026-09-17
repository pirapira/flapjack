#!/usr/bin/env python3
"""Delta-debugging reducer for Pancake sources that expose a parity discrepancy.

This is a C-Reduce-style reducer specialised for the Flapjack parity oracle.
Given a ``.pnk`` source that both compilers accept but compile differently --
or one that they disagree about accepting -- it repeatedly deletes and
simplifies parts of the source, keeping every candidate that still exhibits
the *same* discrepancy, until no further transformation helps.

Nothing about the oracle is reimplemented here.  The original CakeML Pancake
compiler and ``flapjack-compile`` are invoked exactly as
``scripts/parity-small-corpus.py`` invokes them, and the artifact frames are
parsed and classified by ``scripts/parity-bytes.py``, so "the same
discrepancy" means the same thing it means everywhere else in this repository.

Interestingness predicates (``--predicate``)::

    signature       both accept, and the set of differing section names is
                    exactly the seed's set (default; the strictest choice,
                    and the one that stops a reduction from drifting onto a
                    different bug)
    mismatch        both accept and the artifacts differ in any way
    flapjack-reject Cake accepts and Flapjack rejects
    cake-reject     Flapjack accepts and Cake rejects
    disagree        exactly one of the two rejects

Reduction passes, each run to a fixpoint and then the whole sequence repeated
until a full round changes nothing:

    1. strip comments and blank lines
    2. delete brace-balanced line runs (top-level declarations, whole blocks,
       and individual statements all fall out of this one), by halving chunk
       sizes in the usual ddmin schedule
    3. replace a function body with a bare ``return 0;``
    4. simplify integer literals (to 0, to 1, drop the sign, halve)

Outputs, under ``--out`` (default ``parity-reduction``)::

    case.min.pnk    the reduced source
    report.json     predicate, sizes, transformation counts, oracle versions
    replay.sh       a standalone script that recompiles both sides and prints
                    the surviving discrepancy

Only the Python standard library and the scripts already in this repository
are used.
"""

import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CAKE = os.path.expanduser("~/pancake-lean/cakeml/developers/bin/cake")
DEFAULT_FLAPJACK = REPO_ROOT / ".lake" / "build" / "bin" / "flapjack-compile"
PARITY_BYTES = Path(__file__).with_name("parity-bytes.py")


def load_parity_bytes():
    """Import ``parity-bytes.py`` by path; its name is not a Python identifier."""
    spec = importlib.util.spec_from_file_location("parity_bytes", PARITY_BYTES)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PB = load_parity_bytes()


# ---------------------------------------------------------------------------
# Oracle
# ---------------------------------------------------------------------------

class Oracle:
    """Compile one source with both compilers and describe the outcome."""

    def __init__(self, cake, flapjack, timeout, nice):
        self.cake = Path(cake)
        self.flapjack = Path(flapjack)
        self.timeout = timeout
        self.nice = nice
        self.calls = 0

    def _prefix(self):
        return ["nice", "-n", str(self.nice)] if self.nice else []

    def compile_cake(self, path):
        command = self._prefix() + [str(self.cake), "--pancake", "--target=riscv"]
        with path.open("rb") as stream:
            return subprocess.run(command, stdin=stream, capture_output=True,
                                  timeout=self.timeout)

    def compile_flapjack(self, path):
        command = self._prefix() + [str(self.flapjack), "--assembly", str(path)]
        return subprocess.run(command, capture_output=True, timeout=self.timeout)

    def observe(self, path):
        """Return a dict describing this source's parity outcome."""
        self.calls += 1
        try:
            cake = self.compile_cake(path)
            flapjack = self.compile_flapjack(path)
        except subprocess.TimeoutExpired:
            return {"status": "timeout"}
        cake_ok = cake.returncode == 0
        flapjack_ok = flapjack.returncode == 0
        outcome = {"cake_accepted": cake_ok, "flapjack_accepted": flapjack_ok}
        if not (cake_ok and flapjack_ok):
            outcome["status"] = "rejected"
            return outcome
        cake_sections = PB.parse_assembly(cake.stdout.decode(errors="replace"))
        flapjack_sections = PB.parse_assembly(flapjack.stdout.decode(errors="replace"))
        if cake_sections is None or flapjack_sections is None:
            outcome["status"] = "unparsed"
            return outcome
        _, cake_entry, cake_user = PB.classify(cake_sections)
        _, flapjack_entry, flapjack_user = PB.classify(flapjack_sections)
        differing = sorted(
            name for name in set(cake_user) | set(flapjack_user)
            if cake_user.get(name, (None, None, None))[2]
            != flapjack_user.get(name, (None, None, None))[2])
        entry_differs = (cake_entry or (None, None, None))[2] != \
            (flapjack_entry or (None, None, None))[2]
        outcome.update({
            "status": "compiled",
            "differing_sections": differing,
            "entry_differs": entry_differs,
            "identical": not differing and not entry_differs,
            "cake_sha256": hashlib.sha256(cake.stdout).hexdigest(),
            "flapjack_sha256": hashlib.sha256(flapjack.stdout).hexdigest(),
        })
        return outcome


def signature(outcome):
    """The comparable part of an outcome, for the ``signature`` predicate."""
    if outcome.get("status") != "compiled":
        return None
    return (tuple(outcome["differing_sections"]), outcome["entry_differs"])


PREDICATES = {}


def predicate(name):
    def register(function):
        PREDICATES[name] = function
        return function
    return register


@predicate("signature")
def _signature(outcome, seed):
    return signature(outcome) is not None and signature(outcome) == signature(seed)


@predicate("mismatch")
def _mismatch(outcome, _seed):
    return outcome.get("status") == "compiled" and not outcome["identical"]


@predicate("section")
def _section(outcome, seed):
    """Both accept and the named section (``--section``) still differs.

    The `signature` predicate is the right default for a case with a handful
    of differing sections, but an input such as the stateless guest differs in
    hundreds at once; requiring all of them to survive prevents any reduction.
    Naming one section reduces towards that section's discrepancy alone.
    """
    target = seed.get("_target_section")
    return outcome.get("status") == "compiled" and \
        target in outcome.get("differing_sections", [])


@predicate("flapjack-reject")
def _flapjack_reject(outcome, _seed):
    return outcome.get("cake_accepted") is True and \
        outcome.get("flapjack_accepted") is False


@predicate("cake-reject")
def _cake_reject(outcome, _seed):
    return outcome.get("flapjack_accepted") is True and \
        outcome.get("cake_accepted") is False


@predicate("disagree")
def _disagree(outcome, _seed):
    return outcome.get("cake_accepted") is not None and \
        outcome.get("flapjack_accepted") is not None and \
        outcome["cake_accepted"] != outcome["flapjack_accepted"]


# ---------------------------------------------------------------------------
# Interestingness test
# ---------------------------------------------------------------------------

class Tester:
    def __init__(self, oracle, predicate_name, seed_outcome, workdir, verbose):
        self.oracle = oracle
        self.predicate = PREDICATES[predicate_name]
        self.seed_outcome = seed_outcome
        self.path = workdir / "candidate.pnk"
        self.cache = {}
        self.verbose = verbose
        self.accepted = 0
        self.rejected = 0

    def interesting(self, text):
        if not text.strip():
            return False
        key = hashlib.sha256(text.encode()).hexdigest()
        if key in self.cache:
            return self.cache[key]
        self.path.write_text(text)
        outcome = self.oracle.observe(self.path)
        verdict = bool(self.predicate(outcome, self.seed_outcome))
        self.cache[key] = verdict
        if verdict:
            self.accepted += 1
        else:
            self.rejected += 1
        if self.verbose:
            print("    probe %s %s" % (key[:8], "keep" if verdict else "drop"),
                  file=sys.stderr)
        return verdict


# ---------------------------------------------------------------------------
# Reduction passes
# ---------------------------------------------------------------------------

def strip_comments(text):
    """Drop ``//`` comments, ``/* */`` comments and blank lines."""
    without_block = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    lines = []
    for line in without_block.splitlines():
        line = re.sub(r"//.*$", "", line)
        if line.strip():
            lines.append(line.rstrip())
    return "\n".join(lines) + "\n"


def brace_balanced(lines):
    """True when this run of lines opens and closes every brace it touches."""
    depth = 0
    for line in lines:
        for character in line:
            if character == "{":
                depth += 1
            elif character == "}":
                depth -= 1
                if depth < 0:
                    return False
    return depth == 0


def pass_delete_runs(text, tester):
    """ddmin over brace-balanced line runs.

    A balanced run is exactly a top-level declaration, a whole block, or a
    single statement, so one pass covers every granularity the task asks for
    without a Pancake parser.
    """
    lines = text.splitlines()
    removed = 0
    chunk = max(1, len(lines) // 2)
    while chunk >= 1:
        start = 0
        progress = False
        while start < len(lines):
            window = lines[start:start + chunk]
            if len(window) == chunk and brace_balanced(window):
                candidate = lines[:start] + lines[start + chunk:]
                if candidate and tester.interesting("\n".join(candidate) + "\n"):
                    lines = candidate
                    removed += chunk
                    progress = True
                    continue
            start += 1
        if not progress:
            chunk //= 2
    return "\n".join(lines) + "\n", removed


FUNCTION_HEADER = re.compile(r"^\s*fun\b[^{]*\{")


def pass_empty_bodies(text, tester):
    """Replace a function body with a bare ``return 0;``."""
    lines = text.splitlines()
    replaced = 0
    index = 0
    while index < len(lines):
        if not FUNCTION_HEADER.match(lines[index]):
            index += 1
            continue
        end = index
        depth = 0
        seen = False
        while end < len(lines):
            for character in lines[end]:
                if character == "{":
                    depth += 1
                    seen = True
                elif character == "}":
                    depth -= 1
            if seen and depth == 0:
                break
            end += 1
        if end >= len(lines) or end == index:
            index += 1
            continue
        header = lines[index][:lines[index].index("{") + 1]
        candidate = lines[:index] + [header, "  return 0;", "}"] + lines[end + 1:]
        if tester.interesting("\n".join(candidate) + "\n"):
            lines = candidate
            replaced += 1
            index += 3
        else:
            index += 1
    return "\n".join(lines) + "\n", replaced


LITERAL = re.compile(r"(?<![\w.])(-?\d+)(?![\w.])")


def literal_candidates(value):
    """Smaller stand-ins for one integer literal, simplest first."""
    options = []
    for option in (0, 1, abs(value), value // 2):
        if option != value and option not in options:
            options.append(option)
    return options


def pass_simplify_literals(text, tester):
    """Shrink integer literals one occurrence at a time."""
    simplified = 0
    while True:
        matches = list(LITERAL.finditer(text))
        for match in matches:
            value = int(match.group(1))
            if value in (0, 1):
                continue
            for option in literal_candidates(value):
                candidate = text[:match.start(1)] + str(option) + text[match.end(1):]
                if tester.interesting(candidate):
                    text = candidate
                    simplified += 1
                    break
            else:
                continue
            break
        else:
            return text, simplified


def parenthesised_spans(text):
    """Every balanced ``(...)`` span, innermost-last, as (start, end) indices."""
    stack = []
    spans = []
    for index, character in enumerate(text):
        if character == "(":
            stack.append(index)
        elif character == ")" and stack:
            start = stack.pop()
            spans.append((start, index + 1))
    return spans


def pass_simplify_expressions(text, tester):
    """Replace a parenthesised subexpression with a constant.

    This is the C-Reduce "replace an expression with a simpler one of the same
    type" move.  Pancake is monomorphic at the word level, so `0` and `1` are
    always well typed where an expression was, and collapsing one operand of a
    large arithmetic tree is usually what turns a fuzzer program into a
    readable repro.  Call argument lists are balanced spans too, so those are
    skipped by requiring the span to sit after an operator or an opening
    delimiter rather than after an identifier.
    """
    simplified = 0
    while True:
        spans = [span for span in parenthesised_spans(text)
                 if span[1] - span[0] > 3]
        spans.sort(key=lambda span: span[0] - span[1])
        for start, end in spans:
            before = text[:start].rstrip()
            if before and (before[-1].isalnum() or before[-1] == "_"):
                continue  # a call argument list, not an expression
            for replacement in ("0", "1"):
                candidate = text[:start] + replacement + text[end:]
                if tester.interesting(candidate):
                    text = candidate
                    simplified += 1
                    break
            else:
                continue
            break
        else:
            return text, simplified


PASSES = [
    ("delete-runs", pass_delete_runs),
    ("empty-bodies", pass_empty_bodies),
    ("simplify-expressions", pass_simplify_expressions),
    ("simplify-literals", pass_simplify_literals),
]


def reduce_source(text, tester, max_rounds, verbose):
    stripped = strip_comments(text)
    if tester.interesting(stripped):
        text = stripped
    counts = {name: 0 for name, _ in PASSES}
    rounds = 0
    while rounds < max_rounds:
        rounds += 1
        before = text
        for name, pass_function in PASSES:
            text, changed = pass_function(text, tester)
            counts[name] += changed
            if verbose:
                print("  round %d pass %-18s %5d bytes" % (rounds, name, len(text)),
                      file=sys.stderr)
        if text == before:
            break
    return text, counts, rounds


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def tool_versions(cake, flapjack):
    def digest(path):
        path = Path(path)
        if not path.is_file():
            return None
        return hashlib.sha256(path.read_bytes()).hexdigest()
    return {"cake": str(cake), "cake_sha256": digest(cake),
            "flapjack": str(flapjack), "flapjack_sha256": digest(flapjack)}


REPLAY_TEMPLATE = """#!/usr/bin/env bash
# Replay the reduced parity discrepancy.  Written by scripts/parity-reduce.py.
#
# Exits 0 while the discrepancy still reproduces and 3 once it is gone, so this
# doubles as a regression check.  Pass another source as $1 to check that one
# instead.  For the full byte-level dump of both artifacts run
#   python3 {repo}/scripts/parity-bytes.py "$source_file"
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source_file="${{1:-$here/case.min.pnk}}"
exec python3 {repo}/scripts/parity-reduce.py "$source_file" \\
  --predicate {predicate} \\
  --expect-sections {sections} \\
  --check-only \\
  --cake "${{CAKE:-{cake}}}" \\
  --flapjack "${{FLAPJACK:-{flapjack}}}"
"""


def write_outputs(out, text, report, cake, flapjack, predicate_name, sections):
    out.mkdir(parents=True, exist_ok=True)
    (out / "case.min.pnk").write_text(text)
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    replay = out / "replay.sh"
    replay.write_text(REPLAY_TEMPLATE.format(
        cake=cake, flapjack=flapjack, repo=REPO_ROOT,
        predicate=predicate_name, sections=",".join(sections) or "(none)"))
    replay.chmod(0o755)
    return replay


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Reduce a Pancake source while preserving a parity discrepancy.")
    parser.add_argument("source", help="the .pnk source to reduce")
    parser.add_argument("--predicate", default="signature", choices=sorted(PREDICATES),
                        help="which discrepancy to preserve (default: signature)")
    parser.add_argument("--out", default="parity-reduction",
                        help="output directory (default: parity-reduction)")
    parser.add_argument("--cake", default=os.environ.get("CAKE", DEFAULT_CAKE))
    parser.add_argument("--flapjack", default=os.environ.get(
        "FLAPJACK", str(DEFAULT_FLAPJACK)))
    parser.add_argument("--timeout", type=int, default=30,
                        help="per-compiler timeout in seconds (default: 30)")
    parser.add_argument("--nice", type=int, default=10,
                        help="nice level for compiler invocations (default: 10)")
    parser.add_argument("--max-rounds", type=int, default=8,
                        help="maximum pass sweeps (default: 8)")
    parser.add_argument("--workdir", default=None)
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--check-only", action="store_true",
                        help="report the seed's outcome and exit without reducing")
    parser.add_argument("--section", default=None,
                        help="section name required by --predicate section")
    parser.add_argument("--expect-sections", default=None,
                        help="comma-separated section names that must be the "
                             "differing set, or '-' for none; turns a "
                             "--check-only run into a regression check")
    args = parser.parse_args(argv)

    source_path = Path(args.source)
    if not source_path.is_file():
        print("missing source: %s" % source_path, file=sys.stderr)
        return 2
    for label, path in (("cake", args.cake), ("flapjack", args.flapjack)):
        if not Path(path).is_file():
            print("missing %s binary: %s" % (label, path), file=sys.stderr)
            return 2

    workdir = Path(args.workdir) if args.workdir else Path(args.out) / ".work"
    workdir.mkdir(parents=True, exist_ok=True)
    if args.predicate == "section" and not args.section:
        print("--predicate section requires --section NAME", file=sys.stderr)
        return 2
    oracle = Oracle(args.cake, args.flapjack, args.timeout, args.nice)
    seed_outcome = oracle.observe(source_path)
    seed_outcome["_target_section"] = args.section
    seed_sections = seed_outcome.get("differing_sections", [])
    print("seed: status=%s cake_accepted=%s flapjack_accepted=%s differing=%d" % (
        seed_outcome.get("status"), seed_outcome.get("cake_accepted"),
        seed_outcome.get("flapjack_accepted"), len(seed_sections)))
    if seed_sections:
        print("seed differing sections: %s" % ", ".join(seed_sections))

    if not PREDICATES[args.predicate](seed_outcome, seed_outcome):
        print("seed does not satisfy predicate %r; nothing to reduce"
              % args.predicate, file=sys.stderr)
        return 3
    if args.expect_sections is not None:
        expected = [] if args.expect_sections.strip() in ("", "-") else \
            [name for name in args.expect_sections.split(",") if name]
        if sorted(expected) != sorted(seed_sections):
            print("expected differing sections %s but observed %s"
                  % (sorted(expected) or "(none)", sorted(seed_sections) or "(none)"),
                  file=sys.stderr)
            return 3
    if args.check_only:
        return 0

    text = source_path.read_text()
    tester = Tester(oracle, args.predicate, seed_outcome, workdir, args.verbose)
    started = time.time()
    reduced, counts, rounds = reduce_source(text, tester, args.max_rounds, args.verbose)
    elapsed = time.time() - started

    final_path = workdir / "final.pnk"
    final_path.write_text(reduced)
    final_outcome = oracle.observe(final_path)
    if not PREDICATES[args.predicate](final_outcome, seed_outcome):
        print("internal error: reduced source lost the discrepancy", file=sys.stderr)
        return 4

    report = {
        "source": str(source_path),
        "predicate": args.predicate,
        "seed": {"bytes": len(text), "lines": len(text.splitlines()),
                 "outcome": seed_outcome},
        "reduced": {"bytes": len(reduced), "lines": len(reduced.splitlines()),
                    "outcome": final_outcome,
                    "sha256": hashlib.sha256(reduced.encode()).hexdigest()},
        "passes": counts,
        "rounds": rounds,
        "oracle_calls": oracle.calls,
        "seconds": round(elapsed, 1),
        "tools": tool_versions(args.cake, args.flapjack),
    }
    out = Path(args.out)
    replay = write_outputs(out, reduced, report, args.cake, args.flapjack,
                           args.predicate, seed_sections)
    shutil.rmtree(workdir, ignore_errors=True)

    print("reduced %d -> %d bytes (%d -> %d lines) in %d oracle calls, %.1fs" % (
        report["seed"]["bytes"], report["reduced"]["bytes"],
        report["seed"]["lines"], report["reduced"]["lines"],
        oracle.calls, elapsed))
    print("passes: %s" % ", ".join("%s=%d" % item for item in counts.items()))
    print("minimized source: %s" % (out / "case.min.pnk"))
    print("replay: %s" % replay)
    return 0


if __name__ == "__main__":
    sys.exit(main())
