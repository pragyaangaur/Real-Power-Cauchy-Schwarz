import Mathlib

open Real intervalIntegral MeasureTheory Set

namespace RealPowerCauchySchwarz

/-- A scalar form of the Cauchy-Schwarz optimisation step. -/
lemma le_sqrt_mul_of_forall {H A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → 2 * l * H ≤ l ^ 2 * A + B) : H ≤ √A * √B := by
  rcases hA.eq_or_lt with hA0 | hApos
  · subst hA0
    by_contra hH
    push Not at hH
    have hH0 : 0 < H := lt_of_le_of_lt (by positivity) hH
    have := h ((B + 1) / H) (by positivity)
    field_simp at this
    nlinarith
  rcases hB.eq_or_lt with hB0 | hBpos
  · subst hB0
    by_contra hH
    push Not at hH
    have hH0 : 0 < H := lt_of_le_of_lt (by positivity) hH
    have := h (H / A) (by positivity)
    field_simp at this
    nlinarith
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 < a ∧ A = a ^ 2 :=
    ⟨√A, Real.sqrt_pos.2 hApos, (Real.sq_sqrt hA).symm⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ B = b ^ 2 :=
    ⟨√B, Real.sqrt_pos.2 hBpos, (Real.sq_sqrt hB).symm⟩
  rw [Real.sqrt_sq ha.le, Real.sqrt_sq hb.le]
  have := h (b / a) (by positivity)
  rw [div_pow] at this
  field_simp at this
  nlinarith [mul_pos ha hb]

/-- Cauchy-Schwarz for interval integrals on `[0,1]`, in the form needed here. -/
lemma integral_le_sqrt_mul {f g h : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (hh : IntervalIntegrable h volume 0 1)
    (f0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) (g0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    (hfg : ∀ x ∈ Icc (0:ℝ) 1, h x ^ 2 ≤ f x * g x) :
    ∫ x in (0:ℝ)..1, h x ≤ √(∫ x in (0:ℝ)..1, f x) * √(∫ x in (0:ℝ)..1, g x) := by
  apply le_sqrt_mul_of_forall
  · exact intervalIntegral.integral_nonneg (by norm_num) f0
  · exact intervalIntegral.integral_nonneg (by norm_num) g0
  intro l hl
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hf.const_mul _) hg]
  apply intervalIntegral.integral_mono_on (by norm_num) (hh.const_mul _)
    ((hf.const_mul _).add hg)
  intro x hx
  have h1 := f0 x hx
  have h2 := g0 x hx
  have h3 := hfg x hx
  by_contra hlt
  push Not at hlt
  have hS : 0 ≤ l ^ 2 * f x + g x := by positivity
  have hT := mul_self_lt_mul_self hS hlt
  nlinarith [sq_nonneg (l ^ 2 * f x - g x), mul_le_mul_of_nonneg_left h3 (sq_nonneg l)]

/-- Inner fundamental theorem of calculus step. -/
lemma inner_rep {p a c : ℝ} (hp : 2 ≤ p) :
    (a + c) ^ (p - 1) - c ^ (p - 1) = (p - 1) * a * ∫ s in (0:ℝ)..1, (s * a + c) ^ (p - 2) := by
  have key := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (f := fun s : ℝ => (s * a + c) ^ (p - 1))
    (f' := fun s => a * (p - 1) * (s * a + c) ^ (p - 1 - 1)) ?_ ?_
  rotate_left
  · intro s _
    have h1 : HasDerivAt (fun s : ℝ => s * a + c) a s := by
        simpa using ((hasDerivAt_id s).mul_const a).add_const c
    exact h1.rpow_const (p := p - 1) (Or.inr (by linarith))
  · apply Continuous.intervalIntegrable
    exact continuous_const.mul (((continuous_id.mul continuous_const).add
      continuous_const).rpow_const (fun _ => Or.inr (by linarith)))
  have e : p - 1 - 1 = p - 2 := by ring
  rw [e, intervalIntegral.integral_const_mul] at key
  simp only [one_mul, zero_mul, zero_add] at key
  rw [← key]; ring

/-- Outer fundamental theorem of calculus step. -/
lemma outer_rep {p a b : ℝ} (hp : 2 ≤ p) :
    (a + b) ^ p - a ^ p - b ^ p
      = p * b * ∫ t in (0:ℝ)..1, ((a + t * b) ^ (p - 1) - (t * b) ^ (p - 1)) := by
  have key := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (f := fun t : ℝ => (a + t * b) ^ p - (t * b) ^ p)
    (f' := fun t => b * p * (a + t * b) ^ (p - 1) - b * p * (t * b) ^ (p - 1)) ?_ ?_
  rotate_left
  · intro t _
    have h1 : HasDerivAt (fun t : ℝ => a + t * b) b t := by
      simpa using ((hasDerivAt_id t).mul_const b).const_add a
    have h2 : HasDerivAt (fun t : ℝ => t * b) b t := by
      simpa using ((hasDerivAt_id t).mul_const b)
    exact (h1.rpow_const (p := p) (Or.inr (by linarith))).sub
      (h2.rpow_const (p := p) (Or.inr (by linarith)))
  · apply Continuous.intervalIntegrable
    refine (continuous_const.mul ?_).sub (continuous_const.mul ?_)
    · exact (continuous_const.add (continuous_id.mul continuous_const)).rpow_const
        (fun _ => Or.inr (by linarith))
    · exact (continuous_id.mul continuous_const).rpow_const (fun _ => Or.inr (by linarith))
  have hp0 : p ≠ 0 := by linarith
  simp only [one_mul, zero_mul, add_zero, Real.zero_rpow hp0, sub_zero] at key
  simp_rw [← mul_sub] at key
  rw [intervalIntegral.integral_const_mul] at key
  linarith

end RealPowerCauchySchwarz
