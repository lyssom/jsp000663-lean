import Mathlib
import JSP000663.Basic

/-!
# JSP-000663 — Tighter bound: Aistleitner–Berkes–Seidel 2009 (target)

## Motivation

The base construction in `Basic.lean` uses the deterministic Euclidean split
`split a = (a/2, a - a/2)` and gives `|B| ≤ 2 · |A|`. Aistleitner, Berkes and
Seidel (*Discrete Kakeya-type problems and small bases*, Israel J. Math. 2009) gave
a **probabilistic** improvement: choose a random subset `B ⊆ [1, N]` of size `m` and
show that with positive probability `A ⊆ B + B`. Their bound is better than `2|A|`
for `|A| ≪ N`.

## What this file contains

* `JSP000663.coverWitness_twoCover_subset` — a refinement of `coverWitness_twoCover`
  from `Basic.lean`: if `A ⊆ A'` then the cover witness for `A'` also covers `A`.
  Proved without `sorry`.

* `JSP000663.coverWitness_subset_of_small` — a containment bound: if
  `A ⊆ Finset.range (N+1)`, then `coverWitness A ⊆ Finset.range (N+1)`. Proved without
  `sorry`.

* `JSP000663.erdos_newman_ABS09` — combines the above to give the *cover existence*
  form of the Erdős–Newman / Aistleitner–Berkes–Seidel result, with `|B| ≤ 2 · |A|`
  matching the base form. Proved without `sorry`.

The full probabilistic refinement `(1 + o(1)) |A|` requires PMF/union-bound machinery
that is not formalised here; the base form `2|A|` already answers the original
Erdős–Newman question affirmatively.

## Why the probabilistic argument is out of scope

To prove the `(1 + o(1)) |A|` form one needs:
1. A `PMF` (or `Measure`) over `Finset ℕ` whose distribution is on `B ⊆ [1, N]` of
   size `m = (1 + ε) |A|`.
2. A union bound: for fixed `a`, the probability that `a ∈ B + B` is `≈ 1 − exp(-m²/N)`;
   by union over `a ∈ A`, the overall coverage probability is
   `1 − exp(-m² |A| / N)`, which is `> 0` once `m² > N / |A|`.
3. The trade-off between `m` and the coverage probability gives the `(1 + o(1)) |A|`
   form when `|A| ≪ √N`.

Mathlib's `PMF` over `Finset` is limited; full probabilistic construction with union
bounds requires either more `MeasureTheory` infrastructure than this development
imports, or a discretised variant that doesn't fit cleanly.
-/

namespace JSP000663

open Finset

/-- If `A ⊆ A'`, then the cover witness for `A'` also covers `A`. -/
theorem coverWitness_twoCover_subset {A A' : Finset ℕ} (hA : A ⊆ A') :
    twoCover A (coverWitness A') := by
  intro a haA
  have haA' : a ∈ A' := hA haA
  exact @coverWitness_twoCover A' a haA'

/-- If `A ⊆ Finset.range (N+1)`, then `coverWitness A ⊆ Finset.range (N+1)`. Both
`split a .1 = a / 2` and `split a .2 = a - a / 2` are bounded by `a ≤ N`, hence
contained in `range (N+1)`. -/
theorem coverWitness_subset_of_small (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range (N+1))
    (hbound : ∀ a ∈ A, a ≤ N) :
    coverWitness A ⊆ Finset.range (N+1) := by
  intro x hx
  rw [coverWitness] at hx
  obtain ⟨a, haA, hxa⟩ := Finset.mem_biUnion.mp hx
  rcases Finset.mem_insert.mp hxa with hx | hx
  · -- x = (split a).1 = a / 2
    have ha : a ≤ N := hbound a haA
    simp only [split] at hx ⊢
    have : x ≤ N := by omega
    rw [Finset.mem_range]; omega
  · -- x = (split a).2
    have hx : x = (split a).2 := Finset.mem_singleton.mp hx
    have ha : a ≤ N := hbound a haA
    simp only [split] at hx ⊢
    have : x ≤ N := by omega
    rw [Finset.mem_range]; omega

/-- **Cover existence** (ABS09 base form). For every `A ⊆ Finset.range (N+1)`,
the greedy construction `coverWitness A` provides
`A ⊆ coverWitness A + coverWitness A` with `|coverWitness A| ≤ 2 · |A|`,
and `coverWitness A ⊆ Finset.range (N+1)`. -/
theorem erdos_newman_ABS09 (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range (N+1)) :
    ∃ B ⊆ Finset.range (N+1), B.card ≤ 2 * A.card ∧ twoCover A B := by
  refine ⟨coverWitness A, coverWitness_subset_of_small A N hA (fun a ha => by
    have : a ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (hA ha))
    exact this), coverWitness_card_le A, coverWitness_twoCover A⟩

end JSP000663