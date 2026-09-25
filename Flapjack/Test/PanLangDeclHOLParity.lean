/-
Oracle parity for the exact HOL `panLang$fun_decl` / `decl` / `struct_info`
carriers (bead flapjack-pxn.18.3.5.8.4).

Rows reproduce `scripts/hol-probes/pan_lang_decl_probe.out`:
  fd_name_len=2 fd_inline=T fd_export=F fd_params_len=2 fd_body_is_skip=T
  d_function_name_len=2 d_decl_name_len=1 d_exn_name_len=2 d_name_fields_len=1
  si_fields_len=1 si_size=7
-/
import Flapjack.Pancake.PanLang.Decl

namespace Flapjack.Test.PanLangDeclHOLParity

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev MlS := Flapjack.Basis.Pure.MlString.MlString
private def s (str : String) : MlS := Flapjack.Basis.Pure.MlString.ofString str
private def w (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

private def fdH : FunDeclHOL 64 :=
  { name := s "AB"
    inline := true
    exported := false
    params := [(s "x", .one), (s "y", .one)]
    body := .skip
    returnShape := .one }

private def expH : ExpHOL 64 := .const (w 5)

private def fdNameLenRow : Bool := fdH.name.explode.length == 2
private def fdInlineRow : Bool := fdH.inline == true
private def fdExportRow : Bool := fdH.exported == false
private def fdParamsLenRow : Bool := fdH.params.length == 2
private def fdBodyIsSkipRow : Bool :=
  match fdH.body with
  | .skip => true
  | _ => false
private def dFunctionNameLenRow : Bool :=
  match (DeclHOL.function fdH : DeclHOL 64) with
  | .function d => d.name.explode.length == 2
  | _ => false
private def dDeclNameLenRow : Bool :=
  match (DeclHOL.decl .one (s "z") expH : DeclHOL 64) with
  | .decl _ name _ => name.explode.length == 1
  | _ => false
private def dExnNameLenRow : Bool :=
  match (DeclHOL.exnDecl (s "ex") .one : DeclHOL 64) with
  | .exnDecl name _ => name.explode.length == 2
  | _ => false
private def dNameFieldsLenRow : Bool :=
  match (DeclHOL.name (s "S") [(s "f", .one)] : DeclHOL 64) with
  | .name _ fields => fields.length == 1
  | _ => false
private def siFieldsLenRow : Bool :=
  (StructInfoHOLExact.mk [(s "f", .one)] 7).fields.length == 1
private def siSizeRow : Bool :=
  (StructInfoHOLExact.mk [] 7).size == 7

private def parityGuard : Bool :=
  fdNameLenRow && fdInlineRow && fdExportRow && fdParamsLenRow && fdBodyIsSkipRow &&
  dFunctionNameLenRow && dDeclNameLenRow && dExnNameLenRow && dNameFieldsLenRow &&
  siFieldsLenRow && siSizeRow

#eval parityGuard
#guard parityGuard

-- kernel-checked roundtrips to the production carriers
example : funDeclToHOL (funDeclOfHOL fdH) = fdH := funDeclToHOL_funDeclOfHOL fdH
example : declToHOL (declOfHOL (DeclHOL.function fdH : DeclHOL 64)) =
    (DeclHOL.function fdH : DeclHOL 64) := declToHOL_declOfHOL _
example : structInfoToHOL (structInfoOfHOL (StructInfoHOLExact.mk [(s "f", .one)] 7)) =
    StructInfoHOLExact.mk [(s "f", .one)] 7 := structInfoToHOL_structInfoOfHOL _

/-! ### Reverse byte-ranged roundtrips (bead .18.3.5.8.5)

Production values over byte-ranged ASCII identifiers round-trip through the
exact MlString carriers and back. -/

private def prodFd : FunDecl (BitVec 64) :=
  { name := "AB"
    inline := true
    exported := false
    params := [("x", Shape.one), ("y", Shape.one)]
    body := Prog.skip
    returnShape := Shape.one }

private theorem prodFdRanged : FunDeclByteRanged prodFd := by
  simp [prodFd, FunDeclByteRanged, ListParamByteRanged, ParamByteRanged,
    NameRanged, ShapeByteRanged, ProgByteRanged]

private def prodDecl : Decl (BitVec 64) := .function prodFd

private def prodSi : StructInfoHOL := { fields := [("f", Shape.one)], size := 7 }

private def prodContext : StructContextHOL := [("S", prodSi)]

example : funDeclOfHOL (funDeclToHOL prodFd) = prodFd :=
  funDeclOfHOL_funDeclToHOL prodFd prodFdRanged
example : declOfHOL (declToHOL prodDecl) = prodDecl :=
  declOfHOL_declToHOL prodDecl (by
    simp [prodDecl, DeclByteRanged, prodFd, FunDeclByteRanged, ListParamByteRanged,
      ParamByteRanged, NameRanged, ShapeByteRanged, ProgByteRanged])
example : structInfoOfHOL (structInfoToHOL prodSi) = prodSi :=
  structInfoOfHOL_structInfoToHOL prodSi (by
    simp [prodSi, StructInfoByteRanged, ListParamByteRanged, ParamByteRanged,
      NameRanged, ShapeByteRanged])
example : structContextOfHOL (structContextToHOL prodContext) = prodContext :=
  structContextOfHOL_structContextToHOL prodContext (by
    simp [prodContext, prodSi, StructContextByteRanged, NameRanged, StructInfoByteRanged,
      ListParamByteRanged, ParamByteRanged, ShapeByteRanged])

end Flapjack.Test.PanLangDeclHOLParity