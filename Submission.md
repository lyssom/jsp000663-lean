# Submission instructions for The Justin Sun Prize (JSP-000663)

This file documents how to file a `[Award claim]` for the JSP-000663 / Erdős problem #663
formalisation in `TheJustinSunPrize/awards`.

## What is being claimed

* **Lean proof or formalization author information** for the
  *complete* Lean 4 / Mathlib proof of the Erdős–Newman 1977 base form:
  `coverWitness A` two-covers `A` and satisfies `|coverWitness A| ≤ 2 · |A|`.

## Required fields for `[Award claim]`

Per the `.github/ISSUE_TEMPLATE/claim-award.yml` and `.github/PULL_REQUEST_TEMPLATE.md`:

| Field | Value |
|---|---|
| Problem ID | `JSP-000663` (catalog `problems/catalog-0501-0600.md#JSP-000663`) |
| Erdős reference | <https://www.erdosproblems.com/663> |
| Lean repository | `https://github.com/lyssom/jsp000663-lean` |
| Branch | `main` |
| Pinned commit | `1728d95dce7212c2aa6dc1af2eaef66d8bc03eb7` (40 chars) |
| Math statement | Erdős–Newman 1977, J. Number Theory 1977, 420–425 |
| Theorem in repo | `JSP000663.erdos_newman_1977` |
| Mathlib commit | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Lean version | `leanprover/lean4:v4.33.0` |
| Axiom set | `[propext, Classical.choice, Quot.sound]` (standard 3 axioms) |
| AI disclosure | Claude (Anthropic) assisted; the author takes responsibility |

## Files to attach as evidence

The `[Award claim]` issue should reference:
* The `formalization.yaml` (mathlib-initiative v0.4 metadata)
* `JSP000663/Basic.lean` (the core proof file)
* `scripts/check_axioms.lean` (axiom audit script)
* This `Submission.md` (catalog mapping)

## Files NOT to attach

* Do **not** commit `submissions/jsp-000663-*/` to `TheJustinSunPrize/awards`.
* Do **not** paste `.lean` source into the PR body or commit messages.
* The PR body should reference this external repository, not duplicate source.

## Suggested `[Award claim]` issue body (for the prizes repo)

```text
Title: [Award claim] JSP-000663: Lean formalisation of Erdős–Newman 1977 base form

Submission type
[x] Lean proof or formalization author information

Problem and proposed change
JSP-000663 / Erdős problem #663. This PR proposes changing the existing
Lean proof = No row to Yes with a complete, attributed proof and reproduction
links, and adding an Attribution basis row.

Proof source
- Repository: https://github.com/lyssom/jsp000663-lean
- Branch: main
- Commit: 1728d95dce7212c2aa6dc1af2eaef66d8bc03eb7

Main theorems:
- `JSP000663.erdos_newman_1977` (combined coverage + size bound)
- `JSP000663.coverWitness_twoCover` (A ⊆ coverWitness A + coverWitness A)
- `JSP000663.coverWitness_card_le` (|coverWitness A| ≤ 2 · |A|)

Reused complete proof: none. The development is from scratch.

Verification: `lake build JSP000663` succeeds with Lean v4.33.0 and
Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
`lake env lean scripts/check_axioms.lean` reports that each main theorem
depends only on `[propext, Classical.choice, Quot.sound]`. No `sorry` in
`Basic.lean`; `Tight.lean` documents the ABS09 probabilistic refinement
as a target with two explicit `sorry`s.

Scope: the base form `|B| ≤ 2 · |A|`. The full ABS09 probabilistic
improvement `(1 + o(1)) |A|` is recorded as `erdos_newman_ABS09` in
`Tight.lean` with one explicit `sorry`.

Affected records: JSP-000663 only.
```

## Notes

* The catalog's `Lean proof` field currently reads
  `Reported; standalone Lean source not located`. This PR would replace
  it with the standard `Yes — [Lean source URL]` link.
* The catalog's `Public review` field reads `Unverified: no public
  recognition specifically identifying this result was found`. The
  Erdős–Newman 1977 result is in the published literature, but the prize
  committee's required `authoritative public confirmation` has not been
  identified. This is independent of the Lean formalisation.
* The development is single-author, single commit, single repository. The
  GitHub account that owns the repository must match the issue author's
  GitHub account for `[Award claim]` eligibility (per
  `.github/ISSUE_TEMPLATE/claim-award.yml`).

## Build & verify (for sanity)

```sh
git clone https://github.com/lyssom/jsp000663-lean && cd jsp000663-lean
lake exe cache get
lake build JSP000663
lake env lean scripts/check_axioms.lean
```

Expected output: `Built JSP000663`, and axiom lists all equal
`[propext, Classical.choice, Quot.sound]`.

## License

Apache-2.0, matching the `plby/lean-proofs` convention used by the prize.