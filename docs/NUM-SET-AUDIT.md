# Audit: HOL `num_set` / `sptree$toAList` vs `WordLangNumSet`

Bead: `flapjack-pxn.18.5.15.1.5` (parent `flapjack-pxn.18.5.15.1`, toward
`compile_to_word_conventions2`). This is a prerequisite audit for porting the
wordConvs predicates that mention `num_set`:
`every_name`, `every_var` (its `Loop` clause), `every_stack_var`,
`wf_names`, `wf_cutsets`, and hence `pre_alloc_conventions` /
`post_alloc_conventions`.

## What HOL defines

- `num_set` is an alias for `unit spt`
  (`cakeml/misc/miscScript.sml:787`, also
  `/home/zksecurity/HOL/src/finite_maps/sptreeScript.sml:31-34`), a canonical
  binary-trie/patricia map.
- `sptree$toAList t = foldi (\k v a. (k,v)::a) 0 []`
  (`sptreeScript.sml:898-899`); it enumerates the map's keys in the trie's
  internal ("mixed-up") order. `MEM (k,v) (toAList t) <=> lookup k t = SOME v`
  (`sptreeScript.sml:920-928`), so it lists each key at most once.
- `sptree$wf` (`sptreeScript.sml:39-44`) is the canonicalisation invariant (no
  branch has two empty children). It is preserved by `insert` and `union`
  (`wf_insert`, `wf_union`).
- `wordConvs$every_name_def` (`wordConvsScript.sml:148-152`) is
  `EVERY P (MAP FST (toAList (FST t))) /\ EVERY P (MAP FST (toAList (SND t)))`.
  `every_var_def`'s `Loop` clause enumerates `names`/`exit_names` the same way.
  `wf_names_def` (`:347`) is `wf (FST t) /\ wf (SND t)`.

## Direct HOL oracle (`scripts/hol-probes/num_set_audit_probe.out`, 16 rows)

| row | value | what it shows |
| --- | --- | --- |
| `ns_empty` | `[]` | empty map enumerates to `[]` |
| `ns_single` | `[(0,())]` | singleton |
| `ns_three_fwd` | `[(1,()); (0,()); (2,())]` | `toAList` order is the trie order, not sorted |
| `ns_three_rev` | `[(1,()); (0,()); (2,())]` | **same for reverse insertion order**: enumeration is canonical, insertion-order independent |
| `ns_insert_dup` | `[(0,())]` | duplicate key collapses |
| `ns_union_dup` | `[(0,())]` | union of equal singletons collapses |
| `ns_mem_yes` / `ns_mem_no` | `T` / `F` | `MEM` is exact domain membership |
| `ns_wf_empty` / `ns_wf_insert` / `ns_wf_union` | `T` / `T` / `T` | `wf` holds for `LN`, `insert`, `union` |
| `ns_name_even_ok` / `ns_name_even_bad` | `T` / `F` | `EVERY P (MAP FST (toAList t))` is the domain conjunction |
| `ns_len_two` | `2` | domain length = number of distinct keys |
| `nsmap_union_left` | `SOME 5` | for non-unit maps `union` is left-biased |
| `nsmap_insert_last` | `SOME 9` | `insert` of an existing key overwrites (last write wins) |

Reproduce with

```
HOL_PROBE_ONLY=num_set_audit_probeScript.sml bash scripts/hol-probes/regenerate.sh
```

(runs from `cakeml/misc/.hol/objs`, which contains `miscTheory`).

## Findings

1. **`toAList` order is never semantically observed by wordConvs.**
   `every_name` and the `Loop` clause of `every_var` consume the enumeration
   only through `EVERY`, which is a conjunction over the listed keys and
   therefore order-insensitive. The oracle's `ns_three_fwd` / `ns_three_rev`
   rows show the order is canonical anyway.
2. **`toAList` never contains duplicates.** It lists each domain key once, so
   duplicate/collapse handling (`ns_insert_dup`, `ns_union_dup`) is invisible
   to the `EVERY`-based predicates. Value-resolution bias (`union`
   left-biased, `insert` last-write) is *not* observed because `num_set`
   values are all `()`.
3. **The wordConvs domain uses are expressible on the existing function
   carrier.** `WordLangNumSet := FiniteMap Nat Unit`, i.e. `Nat -> Option Unit`
   (`Flapjack/Pancake/WordLang.lean`), supports the exact domain conjunction
   without any iteration order:
   `everyNumSetKey P t := forall k, t k = some () -> P k = true`.
4. **`wf` has no function-carrier analogue.** Every `Nat -> Option Unit` is a
   finite map with no "empty branch" notion, so the only function-carrier
   reading of `sptree$wf` is `True`. That is faithful only when every cutset in
   the compiler is produced by `insert`/`union`/`FOLDL insert` (which HOL's
   `wf_insert`/`wf_union` establish). If a downstream theorem *consumes* a
   `wf` hypothesis, dropping it is a statement change and must be recorded,
   not silently tagged.

## Recommended smallest faithful carrier / checked bridge

Keep `WordLangNumSet = FiniteMap Nat Unit` (no broad cutsets rewrite) and use
the order-insensitive domain form, with a checked bridge to an explicit domain
list when a list enumeration is needed. The bridge is in
`Flapjack/Pancake/WordLang.lean` (untagged, just outside the tagged wordConvs
surface):

- `everyNumSetKey P t : Prop := forall k, t k = some () -> P k = true`
  — exact order-insensitive reading of `EVERY P (MAP FST (toAList t))`.
- `numSetDomainList keys t : Prop := keys.Nodup /\ forall k, t k = some () <-> k in keys`
  — the smallest explicit-domain witness.
- `everyNumSetKey_ext` — the domain form respects extensional equality.
- `everyNumSetKey_iff_list` — with a domain witness,
  `everyNumSetKey P t <-> keys.all P = true`, i.e. the function-carrier form is
  equivalent to a concrete list enumeration.

For `wf_names`/`wf_cutsets`, do **not** broad-rewrite cutsets and do **not**
tag a `wf := True` port: first establish (as a separate bead) either that the
compiler always produces `wf` cutsets (carry the invariant) or record the
`wf := True` simplification as a documented mismatch.

## Deliberately not done here

A rewrite of the `WordLangCutsets` carrier to an `sptree`-shaped structure
(with its own enumeration and `wf`) was considered and rejected for this bead:
the oracle shows the order/duplicates it would model are not observed, so the
rewrite would be large infrastructure with no payoff. If a future theorem
needs a genuine `wf` statement, that is the point to introduce it, tracked by
its own bead.
