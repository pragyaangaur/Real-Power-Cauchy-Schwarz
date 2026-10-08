import RealPowerCauchySchwarz.Basic
import RealPowerCauchySchwarz.Equality
import RealPowerCauchySchwarz.Weighted

/-!
# Main statements in the language of `ℝⁿ`

The theorems below restate the equality cases with the Euclidean norm and inner product of
`EuclideanSpace ℝ (Fin n)`, in the same form as `generalized_cauchy_schwarz`.
-/

open Real

namespace RealPowerCauchySchwarz

lemma norm_side_eq_lhs {n : ℕ} (p : ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w)
      = lhs p (fun i => v i) (fun i => w i) := by
  simp only [EuclideanSpace.norm_eq, PiLp.inner_apply, epow, Real.norm_eq_abs, sq_abs,
    RCLike.inner_apply, conj_trivial, lhs]
  congr 1
  simp [mul_comm]

lemma norm_side_eq_rhs {n : ℕ} (p : ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p = rhs p (fun i => v i) (fun i => w i) := by
  simp only [EuclideanSpace.norm_eq, PiLp.inner_apply, Real.norm_eq_abs, sq_abs,
    RCLike.inner_apply, conj_trivial, rhs]
  congr 2
  simp [mul_comm]

/-- **Equality for `p > 2`**, in `ℝⁿ`. Equality holds exactly when `v` and `w` are linearly
dependent, or each has at most one nonzero coordinate. -/
theorem equality_iff_of_two_lt {n : ℕ} {p : ℝ} (hp : 2 < p) (v w : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w) = ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p
      ↔ ((∀ i j, v i * w j = v j * w i) ∨ (∀ i j, i ≠ j → v i * v j = 0 ∧ w i * w j = 0)) := by
  rw [norm_side_eq_lhs, norm_side_eq_rhs]
  exact eq_iff_of_two_lt hp _ _ hv hw

/-- **Equality for `p = 2`**, in `ℝⁿ`. Equality holds exactly when `v` and `w` are linearly
dependent, or both vanish outside two coordinates `i ≠ j` and `v i w i = v j w j`. -/
theorem equality_iff_two {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) :
    ‖epow 2 v‖ * ‖epow 2 w‖ - inner ℝ (epow 2 v) (epow 2 w) = ‖v‖ ^ (2:ℝ) * ‖w‖ ^ (2:ℝ)
        - (inner ℝ v w) ^ (2:ℝ)
      ↔ ((∀ i j, v i * w j = v j * w i) ∨
          ∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → v k = 0 ∧ w k = 0) ∧ v i * w i = v j * w j) := by
  rw [norm_side_eq_lhs, norm_side_eq_rhs]
  exact eq_iff_two _ _ hv hw

end RealPowerCauchySchwarz
