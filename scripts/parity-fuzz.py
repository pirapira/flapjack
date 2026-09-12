#!/usr/bin/env python3
"""Differential fuzzer for original Pancake versus Flapjack.

The script generates random small Pancake source programs and compares how the
original CakeML Pancake compiler and Flapjack's checked source entry point react
to each program:

* ``cake --pancake --target=riscv`` reads the program on standard input.
* ``flapjack-compile`` reads the program from a file.

A *gap* is a program the original Pancake accepts but Flapjack rejects; those
are the high-priority porting bugs.  An *opposite* result is a program the
original rejects but Flapjack accepts; those are recorded separately because
they can reflect permissive (and often intentional) Flapjack behaviour.

Usage::

    scripts/parity-fuzz.py --seed 1 --count 400

The CakeML ``cake`` binary is taken from ``$CAKE`` and otherwise defaults to
``~/pancake-lean/cakeml/developers/bin/cake``.  ``flapjack-compile`` defaults to
this repository's ``.lake/build/bin/flapjack-compile``.  Generated programs are
written under a temporary directory unless ``--out`` is supplied.
"""

import argparse
import os
import random
import subprocess
import sys
import tempfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_CAKE = os.path.expanduser("~/pancake-lean/cakeml/developers/bin/cake")
DEFAULT_FLAPJACK = os.path.join(REPO_ROOT, ".lake", "build", "bin", "flapjack-compile")

CONSTS = ["0", "1", "2", "3", "7", "255", "1000"]
BINOPS = ["+", "-", "*", "&", "|", "^", "<<", ">>", ">>>"]

FIXED = (
    "fun 1 add1(1 a, 1 b) { return a + b; }\n"
    "fun 1 sub1(1 a) { return a - 1; }\n"
    "fun {1,1} pair(1 a, 1 b) { return <a, b>; }\n"
    "struct S { 1 f1, 1 f2 }\n"
    "fun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\n"
    "exception E : 1;\n"
)


class Gen:
    def __init__(self):
        self.words = []
        self.structs = []
        self.pairs = []

    def word(self):
        return random.choice(self.words) if self.words else "x"

    def expr(self, depth=0):
        r = random.random()
        if depth > 2 or r < 0.3:
            if self.words and random.random() < 0.7:
                return random.choice(CONSTS + self.words)
            return random.choice(CONSTS)
        if r < 0.55:
            return "(%s %s %s)" % (self.expr(depth + 1), random.choice(BINOPS), self.expr(depth + 1))
        if r < 0.62:
            return "(%s #>> %s)" % (self.expr(depth + 1), random.choice(["1", "2", "7"]))
        if r < 0.7 and self.structs:
            return "%s.%s" % (random.choice(self.structs), random.choice(["f1", "f2"]))
        if r < 0.76 and self.pairs:
            return "%s.%s" % (random.choice(self.pairs), random.choice(["0", "1"]))
        if r < 0.9:
            return "(lds 1 (%s))" % self.addr(depth + 1)
        return "(ld8 %s)" % self.addr(depth + 1)

    def call(self):
        # In the original Pancake grammar a function application cannot be a
        # sub-expression of an operator, another application, or a shift, so
        # calls are only ever emitted at the top of an expression.
        if random.random() < 0.6:
            return "add1(%s, %s)" % (self.expr(1), self.expr(1))
        return "sub1(%s)" % self.expr(1)

    def top_expr(self):
        if random.random() < 0.35:
            return self.call()
        return self.expr(1)

    def addr(self, depth=0):
        if depth > 2 or random.random() < 0.5:
            return random.choice(["0", "1000", "1008", "1016", "1024", "1000 + 12", "1000 + 24"])
        return "(%s + %s)" % (self.addr(depth + 1), random.choice(["4", "8", "12", "16", "1000"]))

    def cond(self):
        return "(%s %s %s)" % (self.expr(1), random.choice([">", "<", ">=", "<=", "!=", "=="]), self.expr(1))

    def stmt(self, indent):
        p = " " * indent
        r = random.random()
        if r < 0.22 and self.words:
            return p + "%s = %s;" % (random.choice(self.words), self.top_expr())
        if r < 0.3 and self.words:
            return p + "st (%s), %s;" % (self.addr(), self.expr())
        if r < 0.35 and self.words:
            return p + "st8 (%s), %s;" % (self.addr(), self.expr())
        if r < 0.4 and self.words:
            return p + "!stw (%s), %s;" % (self.addr(), self.expr())
        if r < 0.45 and self.words:
            return p + "!ldw %s, (%s);" % (self.word(), self.addr())
        if r < 0.5:
            return p + "@foo(%s, %s, %s, %s);" % (self.expr(), self.expr(), self.expr(), self.expr())
        if r < 0.58:
            body = "\n".join(self.stmt(indent + 2) for _ in range(random.randint(1, 2)))
            other = "\n".join(self.stmt(indent + 2) for _ in range(random.randint(1, 2)))
            return p + "if %s {\n%s\n%s} else {\n%s\n%s}" % (self.cond(), body, p, other, p)
        if r < 0.64:
            body = "\n".join(self.stmt(indent + 2) for _ in range(random.randint(1, 2)))
            extra = random.choice(["", p + "    break;", p + "    continue;"])
            return p + "while (x > 0) {\n%s\n%s\n%s}" % (body, extra, p)
        if r < 0.68:
            return p + "throw E %s;" % self.expr()
        if r < 0.73 and self.words:
            cv = self.word()
            target = self.word()
            inner = "\n".join(self.stmt(indent + 4) for _ in range(random.randint(1, 2)))
            try_body = "%s  %s = %s" % (p, target, self.top_expr())
            return "%stry\n%s\n%scatch E => %s {\n%s\n%s}" % (p, try_body, p, cv, inner, p)
        if self.words:
            return p + "%s = %s;" % (random.choice(self.words), self.top_expr())
        return p + "@foo(%s, %s, %s, %s);" % (self.expr(), self.expr(), self.expr(), self.expr())

    def program(self):
        self.words = ["x"]
        body = ["  var 1 x = %s;" % random.choice(CONSTS)]
        for _ in range(random.randint(0, 2)):
            name = "y%d" % random.randint(0, 999)
            initialiser = self.top_expr()
            self.words.append(name)
            body.append("  var 1 %s = %s;" % (name, initialiser))
        for _ in range(random.randint(0, 1)):
            name = "s%d" % random.randint(0, 999)
            initialiser = "mks(%s, %s)" % (self.expr(), self.expr())
            self.structs.append(name)
            body.append("  var S %s = %s;" % (name, initialiser))
        for _ in range(random.randint(0, 1)):
            name = "p%d" % random.randint(0, 999)
            initialiser = "pair(%s, %s)" % (self.expr(), self.expr())
            self.pairs.append(name)
            body.append("  var {1,1} %s = %s;" % (name, initialiser))
        for _ in range(random.randint(1, 6)):
            body.append(self.stmt(2))
        body.append("  return %s;" % self.top_expr())
        return FIXED + "fun 1 main() {\n" + "\n".join(body) + "\n}\n"


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--seed", type=int, default=1, help="random seed")
    parser.add_argument("--count", type=int, default=400, help="number of programs to generate")
    parser.add_argument("--cake", default=os.environ.get("CAKE", DEFAULT_CAKE), help="path to the CakeML cake binary")
    parser.add_argument("--flapjack", default=os.environ.get("FLAPJACK", DEFAULT_FLAPJACK), help="path to flapjack-compile")
    parser.add_argument("--out", default=None, help="directory for generated programs (default: a temporary directory)")
    parser.add_argument("--quiet", action="store_true", help="do not print individual gaps/opposites")
    args = parser.parse_args(argv)

    if not os.path.exists(args.cake):
        parser.error("cake binary not found at %s (set $CAKE or --cake)" % args.cake)
    if not os.path.exists(args.flapjack):
        parser.error("flapjack-compile not found at %s (set $FLAPJACK or --flapjack)" % args.flapjack)

    random.seed(args.seed)
    scratch_root = "/var/tmp" if os.path.isdir("/var/tmp") else None
    out_dir = args.out or tempfile.mkdtemp(prefix="flapjack-parity-fuzz-", dir=scratch_root)
    os.makedirs(out_dir, exist_ok=True)

    gaps = both_ok = both_bad = opposite = 0
    for i in range(args.count):
        gen = Gen()
        source = gen.program()
        path = os.path.join(out_dir, "f%05d.pan" % i)
        with open(path, "w") as handle:
            handle.write(source)
        cake_code = subprocess.run(
            [args.cake, "--pancake", "--target=riscv"],
            input=source.encode(),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode
        flapjack_code = subprocess.run(
            [args.flapjack, path],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode
        if cake_code == 0 and flapjack_code != 0:
            gaps += 1
            if not args.quiet:
                print("GAP", path)
                print(source)
        elif cake_code != 0 and flapjack_code == 0:
            opposite += 1
            if not args.quiet and opposite <= 5:
                print("OPPOSITE", path)
                print(source)
        elif cake_code == 0 and flapjack_code == 0:
            both_ok += 1
        else:
            both_bad += 1

    print(
        "seed=%d count=%d both_ok=%d both_bad=%d gaps=%d opposite=%d out=%s"
        % (args.seed, args.count, both_ok, both_bad, gaps, opposite, out_dir)
    )
    return 1 if gaps else 0


if __name__ == "__main__":
    sys.exit(main())
