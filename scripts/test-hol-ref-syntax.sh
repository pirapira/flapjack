#!/usr/bin/env bash
set -euo pipefail

# Compile throwaway declarations so syntax tests do not create false HOL ports
# in the repository's declaration inventory.
root_dir=$(cd "$(dirname "$0")/.." && pwd)
cd "$root_dir"
lake build Flapjack.HolRef >/dev/null
test_file=$(mktemp --suffix=.lean)
trap 'rm -f "$test_file"' EXIT

printf '%s\n' \
  'import Flapjack.HolRef' \
  'open Flapjack' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def"]' \
  'theorem exactSyntax : True := trivial' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def" (list_as_array := [degrees])]' \
  'theorem qualifiedSyntax : True := trivial' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def" 252 (list_as_array := [degrees, moves])]' \
  'theorem qualifiedLineSyntax : True := trivial' \
  '#hol_refs' > "$test_file"
output=$(lake env lean "$test_file")
[[ "$output" == *'qualifiedSyntax  cakeml/compiler/backend/reg_alloc/reg_allocScript.sml  dec_deg_def (list_as_array := [degrees])'* ]]
[[ "$output" == *'qualifiedLineSyntax  cakeml/compiler/backend/reg_alloc/reg_allocScript.sml  dec_deg_def :252 (list_as_array := [degrees, moves])'* ]]
[[ "$output" == *'exactSyntax  cakeml/compiler/backend/reg_alloc/reg_allocScript.sml  dec_deg_def'* ]]

printf '%s\n' \
  'import Flapjack.HolRef' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def" (list_as_array := [])]' \
  'theorem emptyQualifier : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'empty list_as_array qualifier was accepted' >&2
  exit 1
fi

printf '%s\n' \
  'import Flapjack.HolRef' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def" (list_as_array := [degrees, degrees])]' \
  'theorem duplicateFields : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'duplicate list_as_array fields were accepted' >&2
  exit 1
fi

echo 'HOL reference attribute syntax: exact and qualified forms pass; invalid qualifiers rejected'
