import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

class NativeInstructionCodecTests(unittest.TestCase):
    def test_exhaustive_production_cases(self):
        model = (ROOT / "Flapjack/RiscV/Model.lean").read_text().split("inductive Instruction (width : Nat) where", 1)[1].split("deriving DecidableEq, Repr", 1)[0]
        codec = (ROOT / "Flapjack/RiscV/Encoding/NativeInstruction.lean").read_text().split("def nativeInstructionAtWidth", 1)[1].split("/-- Universal byte-order", 1)[0]
        expected = re.findall(r"^  \| (\w+)", model, re.M)
        actual = re.findall(r"^  \| \.(\w+)", codec, re.M)
        self.assertEqual(actual, expected)
        self.assertEqual(len(set(actual)), len(actual))
        self.assertNotIn("| _", codec)
        self.assertNotIn("holArb", codec)

    def test_executed_native_route_has_no_legacy_encoder(self):
        runtime = (ROOT / "Flapjack/RiscV/Encoding.lean").read_text()
        word = runtime.split("def encodeInstruction {", 1)[1].split("def encodeWordBytes", 1)[0]
        byte = runtime.split("def encodeInstructionBytes", 1)[1].split("def encodeInstructions", 1)[0]
        self.assertIn("if h : width = 64", word)
        self.assertIn("L3.Encode (nativeInstruction (h ▸ i))", word)
        self.assertIn("Target.riscvEncode (nativeInstruction (h ▸ instruction))", byte)
        self.assertNotIn("EncodingReference", runtime)
        for helper in ["encodeR", "encodeIValue", "encodeS", "encodeB", "encodeU", "encodeJ"]:
            self.assertNotRegex(runtime, r"\bdef " + helper + r"\b")
        reference = (ROOT / "Flapjack/RiscV/Encoding/Reference.lean").read_text()
        self.assertNotRegex(reference, r"(?m)^def ")
        self.assertIn("noncomputable def encodeInstructionWeighted", reference)

    def test_all_constructor_kernel_regressions(self):
        codec = (ROOT / "Flapjack/RiscV/Encoding/NativeInstruction.lean").read_text()
        names = re.findall(r"^  \| \.(\w+)", codec, re.M)
        tests = (ROOT / "Flapjack/Test/RiscVNativeInstructionParity.lean").read_text()
        for name in names:
            samples = re.findall(
                r"example : EncodingReference\.encodeInstructionWeighted \(width := 64\)"
                r" \(Instruction\." + name + r"[ )][^\n]*= L3\.Encode \(nativeInstruction",
                tests,
            )
            self.assertEqual(len(samples), 3, name)
        self.assertEqual(tests.count(":= by decide"), 3 * len(names))
        for opcode in ["SB", "SH", "SW", "SD"]:
            self.assertIn(".Store (." + opcode + " (nativeRegister a, nativeRegister d,", codec)
        self.assertNotIn("@[hol", codec)

if __name__ == "__main__":
    unittest.main()
