module

public import Mathlib

@[expose] public section

/-!
# A Cauchy-Schwarz inequality for real powers: the statements

This file is the statement surface for Palomar. It imports only Mathlib, and every theorem in it
is left as `sorry`. `Solution.lean` proves each one, and `comparator.json` lists them.

For a vector `v ∈ ℝⁿ` and a real number `p`, write `v^p` for the vector whose entries are the real
powers `v i ^ p` (`Real.rpow`). Norms and inner products are the Euclidean ones of
`EuclideanSpace ℝ (Fin n)`.

Johnston, Plosker, Torrance and Varona (arXiv:2507.10327, Conjecture 5.1) conjectured that
`‖v^p‖ ‖w^p‖ - ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p - ⟨v, w⟩^p` for every real `p ≥ 2` and all vectors with
positive entries. They proved it for integer `p` and showed that it fails for `1 < p < 2`.

* `conjecture_5_1` is the conjecture as they state it, with positive entries.
* `inequality` proves it under the weaker hypothesis of nonnegative entries.
* `equality_cases_of_two_lt` and `equality_cases_two` give every case of equality, for `p > 2` and
  for `p = 2`.
* `weighted_characterisation` says which positive weights `ω` make the weighted form of the
  inequality true, where coordinate `i` carries weight `ω i` in every norm and inner product.
-/

open Real

namespace RealPowerCauchySchwarz

/-- The entrywise real power `v^p` of a vector `v ∈ ℝⁿ`: its `i`-th entry is `v i ^ p`, computed
with `Real.rpow`. -/
noncomputable def epow {n : ℕ} (p : ℝ) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => v i ^ p)

/-- **Conjecture 5.1 of Johnston, Plosker, Torrance and Varona**, as they state it. For every real
`p ≥ 2` and all `v, w ∈ ℝⁿ` with positive entries,
`‖v^p‖ ‖w^p‖ - ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p - ⟨v, w⟩^p`. -/
theorem conjecture_5_1 {n : ℕ} (p : ℝ) (hp : 2 ≤ p) (v w : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w)
      ≤ ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p := by
  sorry

/-- **The inequality for nonnegative vectors.** For every real `p ≥ 2` and all `v, w ∈ ℝⁿ` with
nonnegative entries, `‖v^p‖ ‖w^p‖ - ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p - ⟨v, w⟩^p`. This contains
`conjecture_5_1`. -/
theorem inequality (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (v w : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w)
      ≤ ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p := by
  sorry

/-- **Equality for `p > 2`.** For real `p > 2` and `v, w ∈ ℝⁿ` with nonnegative entries, equality
holds exactly when every `2 × 2` minor `v i w j - v j w i` vanishes (so `v` and `w` are linearly
dependent), or when each of `v` and `w` has at most one nonzero entry. -/
theorem equality_cases_of_two_lt {n : ℕ} {p : ℝ} (hp : 2 < p) (v w : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w) = ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p
      ↔ ((∀ i j, v i * w j = v j * w i) ∨ (∀ i j, i ≠ j → v i * v j = 0 ∧ w i * w j = 0)) := by
  sorry

/-- **Equality for `p = 2`.** For `v, w ∈ ℝⁿ` with nonnegative entries, equality holds with
`p = 2` exactly when `v` and `w` are linearly dependent, or when there are two different indices
`i ≠ j` outside which both vectors vanish and `v i w i = v j w j`. -/
theorem equality_cases_two {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) :
    ‖epow 2 v‖ * ‖epow 2 w‖ - inner ℝ (epow 2 v) (epow 2 w) = ‖v‖ ^ (2:ℝ) * ‖w‖ ^ (2:ℝ)
        - (inner ℝ v w) ^ (2:ℝ)
      ↔ ((∀ i j, v i * w j = v j * w i) ∨
          ∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → v k = 0 ∧ w k = 0) ∧ v i * w i = v j * w j) := by
  sorry

/-- **The weighted inequality, characterised.** Give coordinate `i` a weight `ω i > 0` and use the
weighted norm `‖x‖_ω = √(∑ ω i x i ^ 2)` and inner product `⟨x, y⟩_ω = ∑ ω i x i y i`. For every
real `p ≥ 2`, the inequality `‖v^p‖_ω ‖w^p‖_ω - ⟨v^p, w^p⟩_ω ≤ ‖v‖_ω^p ‖w‖_ω^p - ⟨v, w⟩_ω^p` holds
for all `v, w` with nonnegative entries if and only if `ω i ω j ≥ 1` for all `i ≠ j`. The
condition does not depend on `p`. -/
theorem weighted_characterisation {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (p : ℝ)
    (hp : 2 ≤ p) :
    (∀ v w : Fin n → ℝ, (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ w i) →
      √(∑ i, ω i * (v i ^ p) ^ 2) * √(∑ i, ω i * (w i ^ p) ^ 2) - ∑ i, ω i * (v i ^ p * w i ^ p)
        ≤ (√(∑ i, ω i * v i ^ 2)) ^ p * (√(∑ i, ω i * w i ^ 2)) ^ p
          - (∑ i, ω i * (v i * w i)) ^ p) ↔
      ∀ i j, i ≠ j → 1 ≤ ω i * ω j := by
  sorry

end RealPowerCauchySchwarz
