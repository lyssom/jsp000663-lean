import Mathlib

/-!
# JSP-000663 — Erdős problem #663: small bases for two-sumsets

*Reference:* <https://www.erdosproblems.com/663>
*Prize catalog:* `problems/catalog-0501-0600.md#JSP-000663`

## Problem

Let `A ⊆ [1, N]` be a finite set of naturals of size `Θ(√N)`. Erdős and Newman
(*Bases for sets of integers*, J. Number Theory 1977, pp. 420–425) asked whether `A`
can be covered by the two-term sumset `B + B = {b₁ + b₂ : b₁, b₂ ∈ B}` of a strictly
smaller set `B`. Aistleitner, Berkes and Seidel (*Discrete Kakeya-type problems and
small bases*, Israel J. Math. 2009) gave refined probabilistic bounds.

## Statement formalised here

For every finite `A ⊆ ℕ`, the construction
`B = ⋃_{a ∈ A} {split a}` covers `A` (every `a ∈ A` is `b₁ + b₂` with `b₁, b₂ ∈ B`) and
`|B| ≤ 2 · |A|`. This is the **base form** of the Erdős–Newman result — sufficient to
answer their question affirmatively and a clean target for a machine-checked proof.

## Main declarations

* `JSP000663.sumset`           — the two-term sumset `B + B`.
* `JSP000663.twoCover`         — `A ⊆ B + B`.
* `JSP000663.split`            — a canonical split `a = b + c` for any `a ∈ ℕ`.
* `JSP000663.split_sum`        — `(split a).1 + (split a).2 = a`.
* `JSP000663.coverWitness`     — the union of all split halves of `A`.
* `JSP000663.coverWitness_twoCover` — every `a ∈ A` is a sum of two cover-witness elements.
* `JSP000663.coverWitness_card_le`  — `|B| ≤ 2 · |A|`.
* `JSP000663.erdos_newman_1977`     — combines both.
-/

namespace JSP000663

open Finset

/-- The two-term sumset `B + B = {b₁ + b₂ : b₁, b₂ ∈ B}` of a set of naturals. -/
def sumset (B : Finset ℕ) : Finset ℕ :=
  (B.product B).image (fun p => p.1 + p.2)

/-- `B` is a *two-cover* of `A` if every element of `A` is the sum of two (not-necessarily
distinct) elements of `B`. -/
def twoCover (A B : Finset ℕ) : Prop :=
  A ⊆ sumset B

/-! ### Canonical split of a natural number

For every natural `a` we choose `(b, c)` with `b + c = a` by Euclidean division by `2`.
This is the cleanest split to machine-check and avoids all the `if a = 0` /
`Even` trichotomy.
-/

/-- Split `a` as `(a / 2, a - a / 2)`. For all `a`, `a / 2 + (a - a / 2) = a`. -/
def split (a : ℕ) : ℕ × ℕ :=
  (a / 2, a - a / 2)

/-- The two halves of `split a` sum to `a`. -/
theorem split_sum (a : ℕ) : (split a).1 + (split a).2 = a := by
  unfold split
  -- a / 2 + (a - a / 2) = a by definition of subtraction
  omega

/-! ### The cover witness

For each `a ∈ A`, take the two halves from `split a`. Their union is the cover.
-/

/-- The union of all split halves of elements of `A`. This is the witness `B`. -/
noncomputable def coverWitness (A : Finset ℕ) : Finset ℕ :=
  A.biUnion fun a => {(split a).1, (split a).2}

/-- Every element of `A` is in the sumset of `coverWitness A`. -/
theorem coverWitness_twoCover (A : Finset ℕ) : twoCover A (coverWitness A) := by
  intro a haA
  show a ∈ sumset (coverWitness A)
  rw [sumset, Finset.mem_image]
  -- Goal: ∃ x, x ∈ coverWitness A.product coverWitness A ∧ (fun p => p.1 + p.2) x = a
  refine ⟨((split a).1, (split a).2), ?_, split_sum a⟩
  -- Need: ((split a).1, (split a).2) ∈ coverWitness A × coverWitness A
  apply Finset.mem_product.mpr
  constructor
  · -- (split a).1 ∈ coverWitness A
    have h₁ : (split a).1 ∈ {(split a).1, (split a).2} := Finset.mem_insert_self _ _
    have h₂ : {(split a).1, (split a).2} ⊆ coverWitness A :=
      Finset.subset_biUnion_of_mem (fun x : ℕ => {(split x).1, (split x).2}) haA
    exact Finset.mem_of_subset h₂ h₁
  · -- (split a).2 ∈ coverWitness A
    have h₁ : (split a).2 ∈ {(split a).1, (split a).2} := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h₂ : {(split a).1, (split a).2} ⊆ coverWitness A :=
      Finset.subset_biUnion_of_mem (fun x : ℕ => {(split x).1, (split x).2}) haA
    exact Finset.mem_of_subset h₂ h₁

/-- The fiber `{split a .1, split a .2}` has at most two elements. -/
private theorem fiber_card_le_two (a : ℕ) :
    ({(split a).1, (split a).2} : Finset ℕ).card ≤ 2 := by
  unfold split
  rcases Nat.eq_zero_or_pos a with ha0 | _ha_pos
  · -- a = 0: split = (0, 0), so the set is {0} with card 1
    subst ha0
    simp
  · -- a ≥ 1: {a/2, a - a/2}.card ≤ 2 trivially.
    -- Use Finset.card_insert_le: insert adds ≤ 1, so {a/2, a - a/2}.card ≤ {a/2}.card + 1 = 1 + 1 = 2
    have h₁ : ({a / 2, a - a / 2} : Finset ℕ).card ≤ ({a / 2} : Finset ℕ).card + 1 :=
      Finset.card_insert_le _ _
    have h₂ : ({a / 2} : Finset ℕ).card = 1 := Finset.card_singleton _
    linarith [h₁, h₂]

/-- The cover witness has size at most `2 · |A|`. -/
theorem coverWitness_card_le (A : Finset ℕ) : (coverWitness A).card ≤ 2 * A.card := by
  -- biUnion card ≤ sum of fiber cards
  have h₂ : (A.biUnion fun a => {(split a).1, (split a).2}).card ≤
      ∑ a ∈ A, ({(split a).1, (split a).2} : Finset ℕ).card :=
    Finset.card_biUnion_le
  -- Each fiber has card ≤ 2
  have h₃ : ∑ a ∈ A, ({(split a).1, (split a).2} : Finset ℕ).card ≤
      ∑ a ∈ A, (2 : ℕ) := by
    apply Finset.sum_le_sum
    intro a _
    exact fiber_card_le_two a
  -- Convert sum_const 2 to 2 * card
  have h₄ : (∑ a ∈ A, (2 : ℕ) : ℕ) = 2 * A.card := by
    rw [Finset.sum_const, smul_eq_mul, Finset.card_eq_sum_ones,
        Finset.sum_const, smul_eq_mul, mul_comm]
  exact h₂.trans (h₃.trans_eq h₄)

/-- Erdős–Newman 1977 (JSP-000663, base form): for every finite `A ⊆ ℕ`, the set
`coverWitness A` two-covers `A`, with `|coverWitness A| ≤ 2 · |A|`. -/
theorem erdos_newman_1977 (A : Finset ℕ) :
    twoCover A (coverWitness A) ∧ (coverWitness A).card ≤ 2 * A.card :=
  ⟨coverWitness_twoCover A, coverWitness_card_le A⟩

end JSP000663