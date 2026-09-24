import Flapjack.Pancake.PanLang.Prog

/-!
Parity fixture for the exact `panLang$prog` carrier
(`Flapjack/Pancake/PanLang/Prog.lean`, `ProgHOL`).

The rows reproduce the direct HOL EVAL fixture
`scripts/hol-probes/pan_lang_prog_probe.out`, which evaluates `panLang$prog`
constructors at the HOL numeral word type 64 and pins the `mlstring` name fields
and constructor arities.  Lean-side we build the same `ProgHOL` values and read
back the corresponding payloads/arities.
-/

namespace Flapjack.Test.PanLangProgHOLParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

private def ofString := Flapjack.Basis.Pure.MlString.ofString

private abbrev P := ProgHOL 64

private def c (n : Nat) : ExpHOL 64 := .const (BitVec.ofNat 64 n)

private def kindCode : VarKind → Nat
  | .local => 0
  | .global => 1

private def sizeCode : OpSize → Nat
  | .op8 => 1
  | .opW => 2
  | .op32 => 3
  | .op16 => 4

/-- Row `pg_skip`. -/
private def skipRow : Bool :=
  match ((.skip) : P) with
  | .skip => true
  | _ => false

/-- Row `pg_dec_name_len`: `Dec (strlit "a") _ _ _` has name length `1`. -/
private def decNameLenRow : Bool :=
  match ((.dec (ofString "a") .one (c 1) .skip) : P) with
  | .dec nm _ _ _ => nm.explode.length = 1
  | _ => false

/-- Row `pg_assign_kind`: `Assign Local _ _` has kind code `0`. -/
private def assignKindRow : Bool :=
  match ((.assign .local (ofString "x") (c 1)) : P) with
  | .assign k _ _ => kindCode k = 0
  | _ => false

/-- Row `pg_primitive_args_len`: `Primitive _ _ [_, _]` has arity `2`. -/
private def primitiveArgsLenRow : Bool :=
  match ((.primitive (ofString "p") .addCarry [c 1, c 2]) : P) with
  | .primitive _ _ args => args.length = 2
  | _ => false

/-- Row `pg_store`. -/
private def storeRow : Bool :=
  match ((.store (c 1) (c 2)) : P) with
  | .store _ _ => true
  | _ => false

/-- Row `pg_seq`. -/
private def seqRow : Bool :=
  match ((.seq .skip .skip) : P) with
  | .seq _ _ => true
  | _ => false

/-- Row `pg_if`. -/
private def ifRow : Bool :=
  match ((.ite (c 1) .skip .skip) : P) with
  | .ite _ _ _ => true
  | _ => false

/-- Row `pg_while`. -/
private def whileRow : Bool :=
  match ((.while (c 1) .skip) : P) with
  | .while _ _ => true
  | _ => false

/-- Row `pg_break`. -/
private def breakRow : Bool :=
  match ((.break) : P) with
  | .break => true
  | _ => false

/-- Row `pg_continue`. -/
private def continueRow : Bool :=
  match ((.continue) : P) with
  | .continue => true
  | _ => false

/-- Row `pg_call_args_len`: `Call _ _ [_, _]` has arity `2`. -/
private def callArgsLenRow : Bool :=
  match ((.call none (ofString "f") [c 1, c 2]) : P) with
  | .call _ _ args => args.length = 2
  | _ => false

/-- Row `pg_deccall_args_len`: `DecCall _ _ _ [_, _] _` has arity `2`. -/
private def decCallArgsLenRow : Bool :=
  match ((.decCall (ofString "x") .one (ofString "f") [c 1, c 2] .skip) : P) with
  | .decCall _ _ _ args _ => args.length = 2
  | _ => false

/-- Row `pg_extcall_name_len`: `ExtCall (strlit "abc") _ _ _ _` name length `3`. -/
private def extCallNameLenRow : Bool :=
  match ((.extCall (ofString "abc") (c 1) (c 2) (c 3) (c 4)) : P) with
  | .extCall nm _ _ _ _ => nm.explode.length = 3
  | _ => false

/-- Row `pg_raise_eid_len`: `Raise (strlit "ab") _` eid length `2`. -/
private def raiseEidLenRow : Bool :=
  match ((.raise (ofString "ab") (c 1)) : P) with
  | .raise eid _ => eid.explode.length = 2
  | _ => false

/-- Row `pg_return`. -/
private def returnRow : Bool :=
  match ((.return (c 1)) : P) with
  | .return _ => true
  | _ => false

/-- Row `pg_shmemload_size`: `ShMemLoad Op8 _ _ _` size code `1`. -/
private def shMemLoadSizeRow : Bool :=
  match ((.shMemLoad .op8 .local (ofString "x") (c 1)) : P) with
  | .shMemLoad sz _ _ _ => sizeCode sz = 1
  | _ => false

/-- Row `pg_shmemstore`. -/
private def shMemStoreRow : Bool :=
  match ((.shMemStore .op8 (c 1) (c 2)) : P) with
  | .shMemStore _ _ _ => true
  | _ => false

/-- Row `pg_tick`. -/
private def tickRow : Bool :=
  match ((.tick) : P) with
  | .tick => true
  | _ => false

/-- Row `pg_annot_len`: `Annot (strlit "abcdef") _` tag length `6`. -/
private def annotLenRow : Bool :=
  match ((.annot (ofString "abcdef") (ofString "z")) : P) with
  | .annot tag _ => tag.explode.length = 6
  | _ => false

private def parityGuard : Bool :=
  skipRow && decNameLenRow && assignKindRow && primitiveArgsLenRow && storeRow &&
    seqRow && ifRow && whileRow && breakRow && continueRow && callArgsLenRow &&
    decCallArgsLenRow && extCallNameLenRow && raiseEidLenRow && returnRow &&
    shMemLoadSizeRow && shMemStoreRow && tickRow && annotLenRow

#eval parityGuard
#guard parityGuard

/-- The exact carrier round trips through production syntax and back. -/
example : progToHOL (progOfHOL ((ProgHOL.skip) : P)) = ((ProgHOL.skip) : P) :=
  progToHOL_progOfHOL _

example : progToHOL (progOfHOL ((ProgHOL.annot (ofString "tag") (ofString "body")) : P)) =
    ((ProgHOL.annot (ofString "tag") (ofString "body")) : P) :=
  progToHOL_progOfHOL _

/-- The reverse direction is exact on byte-ranged production programs; this is
the documented side condition. -/
example : progOfHOL (progToHOL (Prog.skip : Prog (BitVec 64))) = (Prog.skip : Prog (BitVec 64)) :=
  progOfHOL_progToHOL _ (by simp [ProgByteRanged])

example : progOfHOL (progToHOL (Prog.return (Exp.const (7 : BitVec 64)) : Prog (BitVec 64))) =
    (Prog.return (Exp.const (7 : BitVec 64)) : Prog (BitVec 64)) :=
  progOfHOL_progToHOL _ (by simp [ProgByteRanged, ExpByteRanged])

example : progOfHOL (progToHOL (Prog.seq (Prog.skip : Prog (BitVec 64)) (Prog.skip : Prog (BitVec 64)) : Prog (BitVec 64))) =
    (Prog.seq (Prog.skip : Prog (BitVec 64)) (Prog.skip : Prog (BitVec 64)) : Prog (BitVec 64)) :=
  progOfHOL_progToHOL _ (by simp [ProgByteRanged])

end Flapjack.Test.PanLangProgHOLParity