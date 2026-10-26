module

public import RealPowerCauchySchwarz

public section

/-!
# A Cauchy-Schwarz inequality for real powers: the proofs

Each theorem below has exactly the statement of its namesake in `Challenge.lean`, and each proof
quotes a theorem of the library `RealPowerCauchySchwarz`. The definition `epow` is the one in
`RealPowerCauchySchwarz.Basic`, which is identical to the definition in `Challenge.lean`.
-/

open Real

namespace RealPowerCauchySchwarz

theorem conjecture_5_1 {n : ℕ} (p : ℝ) (hp : 2 ≤ p) (v w : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w)
      ≤ ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p :=
  generalized_cauchy_schwarz n p hp v w (fun i => (hv i).le) (fun i => (hw i).le)

theorem inequality (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (v w : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w)
      ≤ ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p :=
  generalized_cauchy_schwarz n p hp v w hv hw

theorem equality_cases_of_two_lt {n : ℕ} {p : ℝ} (hp : 2 < p) (v w : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w) = ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p
      ↔ ((∀ i j, v i * w j = v j * w i) ∨ (∀ i j, i ≠ j → v i * v j = 0 ∧ w i * w j = 0)) :=
  equality_iff_of_two_lt hp v w hv hw

theorem equality_cases_two {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) :
    ‖epow 2 v‖ * ‖epow 2 w‖ - inner ℝ (epow 2 v) (epow 2 w) = ‖v‖ ^ (2:ℝ) * ‖w‖ ^ (2:ℝ)
        - (inner ℝ v w) ^ (2:ℝ)
      ↔ ((∀ i j, v i * w j = v j * w i) ∨
          ∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → v k = 0 ∧ w k = 0) ∧ v i * w i = v j * w j) :=
  equality_iff_two v w hv hw

theorem weighted_characterisation {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (p : ℝ)
    (hp : 2 ≤ p) :
    (∀ v w : Fin n → ℝ, (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ w i) →
      √(∑ i, ω i * (v i ^ p) ^ 2) * √(∑ i, ω i * (w i ^ p) ^ 2) - ∑ i, ω i * (v i ^ p * w i ^ p)
        ≤ (√(∑ i, ω i * v i ^ 2)) ^ p * (√(∑ i, ω i * w i ^ 2)) ^ p
          - (∑ i, ω i * (v i * w i)) ^ p) ↔
      ∀ i j, i ≠ j → 1 ≤ ω i * ω j :=
  weighted_iff ω hω p hp

end RealPowerCauchySchwarz
