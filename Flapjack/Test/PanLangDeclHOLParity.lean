/-
Oracle parity for the exact HOL `panLang$fun_decl` / `decl` / `struct_info`
carriers (bead flapjack-pxn.18.3.5.8.4).

Rows reproduce `scripts/hol-probes/pan_lang_decl_probe.out`:
  fd_name_len=2 fd_inline=T fd_export=F fd_params_len=2 fd_body_is_skip=T
  d_function_name_len=2 d_decl_name_len=1 d_exn_name_len=2 d_name_fields_len=1
  si_fields_len=1 si_size=7
-/
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Parser.ParseTopDecsByteRanged
import Flapjack.Pancake.PanGlobals

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

/-! ### Exact-carrier `compile_prog` boundary (bead .18.3.5.8.6)

`compileProgTopHOLOfExact` accepts the MLString-keyed declaration carrier and
agrees with the production compiler on byte-ranged declarations. -/

example :
    compileProgTopHOLOfExact
        (([] : List (Flapjack.Decl (BitVec 64))).map declToHOL) =
      compileProgTopHOL ([] : List (Flapjack.Decl (BitVec 64))) :=
  compileProgTopHOLOfExact_declToHOL [] (by simp)

example :
    compileProgTopHOLOfExact ([prodDecl].map declToHOL) =
      compileProgTopHOL [prodDecl] :=
  compileProgTopHOLOfExact_declToHOL [prodDecl] (by
    intro d hd
    rcases List.mem_singleton.mp hd with rfl
    simp [prodDecl, DeclByteRanged, prodFd, FunDeclByteRanged, ListParamByteRanged,
      ParamByteRanged, NameRanged, ShapeByteRanged, ProgByteRanged])

/-! ### Byte-ranged parser boundary reaches the exact carrier

`ofString`/`toStringOfBytes` is a round trip only on byte-ranged names; a name
with a codepoint `>= 256` (here U+1D518) is truncated, so it still may not be
fed to the exact carrier. The executed parser, however, is byte-faithful
(`utf8Bytes` + HOL-exact ASCII predicates), and `parseTopDecs_declByteRanged`
proves every declaration it returns is `DeclByteRanged`. Composing that with
`compileProgTopHOLOfExact_declToHOL` gives
`parseTopDecs_routes_exactBoundary`: the exact MLString-keyed compiler boundary
applied to the parser output equals the production `compileProgTopHOL`. This is
kernel-proved propositional equality (via the `DeclByteRanged` premise), NOT
definitional equality. The parser-backed production entrypoints now compose
this invariant through the preceding Pancake passes and route the resulting
declaration list through `compileProgTopHOLWithMetadataOfExact`. This is a
carrier-boundary route with source-shaped Crep output, not an exact HOL
`compile_prog` port. Direct original-Pancake parity for the executed boundary
is `python3 scripts/check-parity-goldens.py` (wide_constants.pnk, parity
goldens=1, failures=0). -/
example :
    Flapjack.Basis.Pure.MlString.toStringOfBytes
      (Flapjack.Basis.Pure.MlString.ofString (String.singleton (Char.ofNat 0x1d518))) ≠
    String.singleton (Char.ofNat 0x1d518) := by
  decide

example {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName] [LawfulHashable FunName]
    [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    (ofInt : Int → BitVec width) (source : String) (locations : Bool)
    (declarations : List (Flapjack.Decl (BitVec width)))
    (h : Parser.parseTopDecs ofInt source locations = .ok declarations) :
    compileProgTopHOLOfExact (declarations.map declToHOL) =
      compileProgTopHOL declarations :=
  Parser.parseTopDecs_routes_exactBoundary ofInt source locations declarations h

/-! ### Exact `is_decl` / `is_function` / `functions` append-filter cluster
(beads .1.34, .1.42, .4.81, .4.82, .4.83)

Rows reproduce `scripts/hol-probes/pan_lang_is_function_probe.out`
(`function=T`, `global=F`) and `scripts/hol-probes/pan_lang_functions_probe.out`
(`functions_function`, `functions_global`). -/

private def exactDecls : List (DeclHOL 64) :=
  [ .function fdH, .decl .one (s "z") expH, .name (s "S") [], .exnDecl (s "ex") .one ]

private def exactIsDeclRow : Bool :=
  isDeclHOL (DeclHOL.decl .one (s "z") expH) &&
  !isDeclHOL (DeclHOL.function fdH)

private def exactIsFunctionRow : Bool :=
  isFunctionHOL (DeclHOL.function fdH) &&
  !isFunctionHOL (DeclHOL.decl .one (s "z") expH)

#eval (exactIsDeclRow, exactIsFunctionRow)
#guard exactIsDeclRow && exactIsFunctionRow

example : isDeclHOL (DeclHOL.decl .one (s "z") expH) = true := rfl
example : isDeclHOL (DeclHOL.function fdH) = false := rfl
example : isFunctionHOL (DeclHOL.function fdH) = true := rfl
example : isFunctionHOL (DeclHOL.decl .one (s "z") expH) = false := rfl

/-! Exact `is_name` parity (bead flapjack-4ac.1.36): the HOL-EVAL rows
`is_name_name=T` and `is_name_decl=F` from
`scripts/hol-probes/pan_lang_decl_predicates_probe.out` are replayed over the
exact `DeclHOL` carrier through the tagged `isNameHOL`. -/

private def exactIsNameRow : Bool :=
  isNameHOL (DeclHOL.name (s "S") [] : DeclHOL 64) &&
  !isNameHOL (DeclHOL.decl .one (s "z") expH)

#eval exactIsNameRow
#guard exactIsNameRow

example : isNameHOL (DeclHOL.name (s "S") [] : DeclHOL 64) = true := rfl
example : isNameHOL (DeclHOL.decl .one (s "z") expH) = false := rfl

example :
    functionsHOL (exactDecls ++ exactDecls) =
      functionsHOL exactDecls ++ functionsHOL exactDecls :=
  functionsHOL_append _ _

example : functionsHOL (exactDecls.filter isFunctionHOL) = functionsHOL exactDecls :=
  functionsHOL_filter_isFunction _

example : (functionsHOL (exactDecls.filter isDeclHOL)).length = 0 := by
  simp [functionsHOL_filter_isDecl]

example :
    functionsHOL [DeclHOL.function fdH, DeclHOL.decl .one (s "z") expH] =
      ([DeclHOL.function fdH, DeclHOL.decl .one (s "z") expH].filter
          isFunctionHOL).map
        (fun declaration =>
          match declaration with
          | .function fi => (fi.name, fi.params, fi.body, fi.returnShape)
          | _ =>
              (Flapjack.Basis.Pure.MlString.ofString "",
                [], ProgHOL.skip, ShapeHOL.one)) :=
  functionsHOL_eq_FILTER _

example :
    decsStcnamesHOLExact (width := 64) ([] : StructContextExact)
      [ .function fdH, .decl .one (s "z") expH, .exnDecl (s "ex") .one ] = some [] := by
  apply decsStcnamesHOLExact_of_functions_or_decls_or_exnDecls
  decide

example :
    decsStcnamesHOLExact (width := 64) ([] : StructContextExact)
      [ .function fdH ] = some [] := by
  apply decsStcnamesHOLExact_of_functions
  decide

/-! ## Checked codec bridge to the production predicates (bead flapjack-ni1.1) -/

example (declaration : DeclHOL 64) :
    Flapjack.isDecl (declOfHOL declaration) = isDeclHOL declaration :=
  isDecl_declOfHOL declaration

example (declaration : DeclHOL 64) :
    Flapjack.isExnDecl (declOfHOL declaration) = isExnDeclHOL declaration :=
  isExnDecl_declOfHOL declaration

example (declaration : DeclHOL 64) :
    Flapjack.isName (declOfHOL declaration) = isNameHOL declaration :=
  isName_declOfHOL declaration

example : Flapjack.sizeOfEids (exactDecls.map declOfHOL) =
    (exactDecls.filter isExnDeclHOL).length :=
  sizeOfEids_map_declOfHOL exactDecls

example : Flapjack.sizeOfEids (exactDecls.map declOfHOL) = 1 := by
  rw [sizeOfEids_map_declOfHOL]
  decide

/-! ## Exact `size_of_eids` parity (bead flapjack-4ac.1.37)

The HOL-EVAL rows `size_of_eids_empty=0` and `size_of_eids_mixed=1` from
`scripts/hol-probes/pan_lang_decl_predicates_probe.out` are replayed over the
exact `DeclHOL` carrier through the tagged `sizeOfEidsHOL`. -/

example : sizeOfEidsHOL ([] : List (DeclHOL 64)) = 0 := rfl

example : sizeOfEidsHOL exactDecls = 1 := rfl

example : Flapjack.sizeOfEids (exactDecls.map declOfHOL) = sizeOfEidsHOL exactDecls :=
  sizeOfEids_map_declOfHOL exactDecls

end Flapjack.Test.PanLangDeclHOLParity
