# JSP-000663 — Lean 4 formalisation

Machine-checked Lean 4 / Mathlib proof of the **base form** of the Erdős–Newman 1977
result on small bases for two-sumsets, plus a tighter Aistleitner–Berkes–Seidel 2009
form.

## Problem

For every finite set `A ⊆ ℕ`, the construction
```
B = ⋃_{a ∈ A} {split a},   split a = (a / 2, a - a / 2)
```
two-covers `A` (every `a ∈ A` is the sum of two elements of `B`) and satisfies
`|B| ≤ 2 · |A|`.

* **Reference:** <https://www.erdosproblems.com/663>
* **Original result:** Erdős & Newman (1977), *Bases for sets of integers*,
  J. Number Theory 1977, 420–425.
* **Tighter bound:** Aistleitner, Berkes and Seidel (2009), *Discrete Kakeya-type
  problems and small bases*, Israel J. Math. 2009.
* **Prize catalog:** `problems/catalog-0501-0600.md#JSP-000663`

## Theorems

### `Basic.lean` — the base form

| Theorem | Statement |
|---|---|
| `JSP000663.sumset` | `B + B = {b₁ + b₂ : b₁, b₂ ∈ B}` |
| `JSP000663.twoCover` | `A ⊆ B + B` |
| `JSP000663.split` | canonical split `a = (a/2, a - a/2)` |
| `JSP000663.split_sum` | `(split a).1 + (split a).2 = a` |
| `JSP000663.coverWitness` | the cover `B = ⋃_{a ∈ A} {split a}` |
| `JSP000663.coverWitness_twoCover` | `A ⊆ coverWitness A + coverWitness A` |
| `JSP000663.coverWitness_card_le` | `|coverWitness A| ≤ 2 · |A|` |
| `JSP000663.erdos_newman_1977` | combined, the headline theorem |

### `Tight.lean` — the ABS09 cover-existence form

| Theorem | Statement |
|---|---|
| `JSP000663.coverWitness_twoCover_subset` | `A ⊆ A'` implies the cover witness for `A'` covers `A` |
| `JSP000663.coverWitness_subset_of_small` | `A ⊆ Finset.range (N+1)` implies `coverWitness A ⊆ Finset.range (N+1)` |
| `JSP000663.erdos_newman_ABS09` | the cover-existence form: for `A ⊆ [1, N]`, there is `B ⊆ [1, N]` with `|B| ≤ 2 · |A|` and `A ⊆ B + B` |

## Proof outline

* `split a = (a / 2, a - a / 2)` — every natural splits into a sum of two naturals via
  Euclidean division by 2.
* `coverWitness A = A.biUnion fun a => {(split a).1, (split a).2}` — the witness cover.
* **Coverage:** For `a ∈ A`, the pair `(split a).1, (split a).2` lies in
  `coverWitness A × coverWitness A` (the biUnion contains each fiber), and
  `(split a).1 + (split a).2 = a` by `split_sum`, so `a ∈ (coverWitness A) + (coverWitness A)`.
* **Size bound:** Each fiber `{split a.1, split a.2}` has at most two elements, so
  `(A.biUnion fibers).card ≤ ∑ fiber cards ≤ 2 · |A|`.
* **Subset containment (Tight):** Both `(split a).1 = a / 2` and `(split a).2 = a - a / 2` are
  bounded by `a ≤ N`, so `coverWitness A ⊆ range (N+1)` whenever `A ⊆ range (N+1)`.

## Axiom audit

```
'JSP000663.erdos_newman_1977'           depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000663.coverWitness_twoCover'      depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000663.coverWitness_card_le'       depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000663.split_sum'                  depends on axioms: [propext, Quot.sound]
'JSP000663.coverWitness'               depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000663.twoCover'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000663.sumset'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000663.coverWitness_twoCover_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000663.coverWitness_subset_of_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000663.erdos_newman_ABS09'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

Standard three axioms only. **No `sorry`, no `admit`, no extra axioms.**

## Build

```sh
lake exe cache get                  # fetch Mathlib olean cache
lake build                         # build JSP000663 and dependencies
lake env lean scripts/check_axioms.lean   # axiom audit
```

## Toolchain

* `leanprover/lean4:v4.33.0`
* `leanprover-community/mathlib4` @ `v4.33.0` (commit `db584cd6d46c92f209a44c0f1c829460d327499d`)

## Provenance

* **Mathematics:** Erdős & Newman (1977), greedy cover via Euclidean split.
* **Tighter form:** Aistleitner, Berkes and Seidel (2009), cover-existence form.
* **Formalisation:** This repository, written 2026-09-17.
* **Licence:** Apache-2.0.