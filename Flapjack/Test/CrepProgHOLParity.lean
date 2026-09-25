/-
Direct parity fixture for the exact MlString-backed Crepe program carrier
`Flapjack.CrepProgHOL` (`Flapjack/Pancake/CrepLang/Prog.lean`), the counterpart
of `crepLang$prog` (`cakeml/pancake/crepLangScript.sml:41-66`).

The rows below reproduce the direct HOL EVAL oracle
`scripts/hol-probes/crep_lang_prog_probe.out`, which pins the word payloads,
`MlString` name lengths, and constructor arities at the HOL numeral word type 8.
-/
import Flapjack.Pancake.CrepLang.Prog

namespace Flapjack.Test.CrepProgHOLParity

open Flapjack

private abbrev E8 := CrepProgHOL 8

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n
private def w5 (n : Nat) : BitVec 5 := BitVec.ofNat 5 n
private def nm (s : String) : Flapjack.Basis.Pure.MlString.MlString :=
  Flapjack.Basis.Pure.MlString.ofString s
private def e (n : Nat) : CrepExpHOL 8 := .const (w8 n)

private def prgSkipRow : Bool :=
  match (CrepProgHOL.skip : E8) with | .skip => true | _ => false

private def prgDecRow : Bool :=
  match (.dec 3 (e 5) .skip : E8) with | .dec n _ _ => n == 3 | _ => false

private def prgAssignRow : Bool :=
  match (.assign 4 (e 5) : E8) with | .assign n _ => n == 4 | _ => false

private def prgPrimitiveRow : Bool :=
  match (.primitive [1, 2] PrimOp.addCarry [3] : E8) with
  | .primitive ns _ ms => ns.length + ms.length == 3 | _ => false

private def prgStoreRow : Bool :=
  match (.store (e 1) (e 2) : E8) with | .store _ _ => true | _ => false

private def prgStore32Row : Bool :=
  match (.store32 (e 1) (e 2) : E8) with | .store32 _ _ => true | _ => false

private def prgStoreByteRow : Bool :=
  match (.storeByte (e 1) (e 2) : E8) with | .storeByte _ _ => true | _ => false

private def prgStoreGlobRow : Bool :=
  match (.storeGlob (w5 7) (e 1) : E8) with
  | .storeGlob w _ => w.toNat == 7 | _ => false

private def prgSeqRow : Bool :=
  match (.seq .skip .skip : E8) with | .seq _ _ => true | _ => false

private def prgIfRow : Bool :=
  match (.ite (e 1) .skip .skip : E8) with | .ite _ _ _ => true | _ => false

private def prgWhileRow : Bool :=
  match (.while (e 1) .skip : E8) with | .while _ _ => true | _ => false

private def prgBreakRow : Bool :=
  match (.break 5 : E8) with | .break n => n == 5 | _ => false

private def prgContinueRow : Bool :=
  match (.continue 6 : E8) with | .continue n => n == 6 | _ => false

private def prgCallRow : Bool :=
  match (.call none (nm "f") [e 1] : E8) with
  | .call _ _ args => args.length == 1 | _ => false

private def prgExtCallRow : Bool :=
  match (.extCall (nm "g") 1 2 3 4 : E8) with
  | .extCall f _ _ _ _ => f.explode.length == 1 | _ => false

private def prgRaiseRow : Bool :=
  match (.raise (w8 5) : E8) with | .raise w => w.toNat == 5 | _ => false

private def prgReturnRow : Bool :=
  match (.return [e 1, e 2] : E8) with
  | .return es => es.length == 2 | _ => false

private def prgShMemRow : Bool :=
  match (.shMem CrepMemOp.load8 3 (e 1) : E8) with
  | .shMem _ n _ => n == 3 | _ => false

private def prgTickRow : Bool :=
  match (CrepProgHOL.tick : E8) with | .tick => true | _ => false

def parityGuard : Bool :=
  prgSkipRow && prgDecRow && prgAssignRow && prgPrimitiveRow &&
  prgStoreRow && prgStore32Row && prgStoreByteRow && prgStoreGlobRow &&
  prgSeqRow && prgIfRow && prgWhileRow && prgBreakRow && prgContinueRow &&
  prgCallRow && prgExtCallRow && prgRaiseRow && prgReturnRow &&
  prgShMemRow && prgTickRow

#eval parityGuard
#guard parityGuard

example : crepProgToHOL (crepProgOfHOL (.skip : CrepProgHOL 8)) = .skip :=
  crepProgToHOL_crepProgOfHOL _

example : crepProgOfHOL (crepProgToHOL (.skip : CrepProg (BitVec 8))) = .skip :=
  crepProgOfHOL_crepProgToHOL _ (by simp [CrepProgNameRanged])

end Flapjack.Test.CrepProgHOLParity