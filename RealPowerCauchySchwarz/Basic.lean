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

/-- The superadditivity defect of the entrywise power `t ↦ t ^ p`. -/
noncomputable def G (p a b : ℝ) : ℝ := (a + b) ^ p - a ^ p - b ^ p

/-- The inner integrand after one integration. -/
noncomputable def D (p a b t : ℝ) : ℝ := (a + t * b) ^ (p - 1) - (t * b) ^ (p - 1)

lemma D_continuous {p a b : ℝ} (hp : 2 ≤ p) : Continuous (fun t => D p a b t) := by
  unfold D
  refine Continuous.sub ?_ ?_
  · exact (continuous_const.add (continuous_id.mul continuous_const)).rpow_const
      (fun _ => Or.inr (by linarith))
  · exact (continuous_id.mul continuous_const).rpow_const (fun _ => Or.inr (by linarith))

lemma D_nonneg {p a b t : ℝ} (hp : 2 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    0 ≤ D p a b t := by
  unfold D
  have : (t * b) ^ (p - 1) ≤ (a + t * b) ^ (p - 1) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  linarith

lemma two_mul_le {x1 x2 y1 y2 z1 z2 : ℝ} (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hy1 : 0 ≤ y1)
    (hy2 : 0 ≤ y2)
    (hz1 : z1 ^ 2 ≤ x1 * y1) (hz2 : z2 ^ 2 ≤ x2 * y2) : 2 * z1 * z2 ≤ x1 * y2 + x2 * y1 := by
  have hprod : (z1 * z2) ^ 2 ≤ (x1 * y2) * (x2 * y1) := by
    rw [mul_pow]
    calc z1 ^ 2 * z2 ^ 2 ≤ (x1 * y1) * (x2 * y2) :=
          mul_le_mul hz1 hz2 (sq_nonneg _) (by positivity)
      _ = (x1 * y2) * (x2 * y1) := by ring
  by_contra hlt
  push Not at hlt
  have hS : 0 ≤ x1 * y2 + x2 * y1 := by positivity
  have hT := mul_self_lt_mul_self hS hlt
  nlinarith [sq_nonneg (x1 * y2 - x2 * y1)]

/-- The pointwise inequality for the kernel `(s a + t b) ^ (p - 2)`. -/
lemma kernel_sq_le {p s t x1 x2 y1 y2 z1 z2 : ℝ} (hp : 2 ≤ p) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hy1 : 0 ≤ y1)
    (hy2 : 0 ≤ y2) (hz1' : 0 ≤ z1) (hz2' : 0 ≤ z2)
    (hz1 : z1 ^ 2 ≤ x1 * y1) (hz2 : z2 ^ 2 ≤ x2 * y2) :
    ((s * z1 + t * z2) ^ (p - 2)) ^ 2
      ≤ (s * x1 + t * x2) ^ (p - 2) * (s * y1 + t * y2) ^ (p - 2) := by
  have h0 : 0 ≤ s * z1 + t * z2 := by positivity
  rw [sq, ← Real.mul_rpow h0 h0, ← Real.mul_rpow (by positivity) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  have h2 := two_mul_le hx1 hx2 hy1 hy2 hz1 hz2
  have hst : 0 ≤ s * t := mul_nonneg hs ht
  nlinarith [mul_le_mul_of_nonneg_left hz1 (sq_nonneg s),
    mul_le_mul_of_nonneg_left hz2 (sq_nonneg t), mul_le_mul_of_nonneg_left h2 hst]

lemma kernel_integrable {p : ℝ} (hp : 2 ≤ p) (a c : ℝ) :
    IntervalIntegrable (fun s : ℝ => (s * a + c) ^ (p - 2)) volume 0 1 :=
  (((continuous_id.mul continuous_const).add continuous_const).rpow_const
    (fun _ => Or.inr (by linarith))).intervalIntegrable _ _

lemma D_div_eq {p a b t : ℝ} (hp : 2 ≤ p) (ha : 0 < a) :
    D p a b t / a = (p - 1) * ∫ s in (0:ℝ)..1, (s * a + t * b) ^ (p - 2) := by
  unfold D
  rw [inner_rep hp]
  field_simp

/-- The pointwise (in `t`) Cauchy-Schwarz step after the inner integration. -/
lemma D_sq_le {p t x1 x2 y1 y2 z1 z2 : ℝ} (hp : 2 ≤ p) (ht : t ∈ Icc (0:ℝ) 1)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hy1 : 0 < y1) (hy2 : 0 < y2) (hz1' : 0 < z1) (hz2' : 0 < z2)
    (hz1 : z1 ^ 2 ≤ x1 * y1) (hz2 : z2 ^ 2 ≤ x2 * y2) :
    (D p z1 z2 t / z1) ^ 2 ≤ (D p x1 x2 t / x1) * (D p y1 y2 t / y1) := by
  have ht0 : 0 ≤ t := ht.1
  rw [D_div_eq hp hz1', D_div_eq hp hx1, D_div_eq hp hy1]
  have hnn : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      0 ≤ ∫ s in (0:ℝ)..1, (s * a + t * b) ^ (p - 2) := fun a b ha hb =>
    intervalIntegral.integral_nonneg (by norm_num) (fun s hs => by
      have := hs.1
      positivity)
  have hcs := integral_le_sqrt_mul (kernel_integrable hp x1 (t * x2))
    (kernel_integrable hp y1 (t * y2)) (kernel_integrable hp z1 (t * z2))
    (fun s hs => by have := hs.1; positivity) (fun s hs => by have := hs.1; positivity)
    (fun s hs => kernel_sq_le hp hs.1 ht0 hx1.le hx2.le hy1.le hy2.le hz1'.le hz2'.le hz1 hz2)
  set Iz := ∫ s in (0:ℝ)..1, (s * z1 + t * z2) ^ (p - 2)
  set Ix := ∫ s in (0:ℝ)..1, (s * x1 + t * x2) ^ (p - 2)
  set Iy := ∫ s in (0:ℝ)..1, (s * y1 + t * y2) ^ (p - 2)
  have hIz : 0 ≤ Iz := hnn z1 z2 hz1'.le hz2'.le
  have hIx : 0 ≤ Ix := hnn x1 x2 hx1.le hx2.le
  have hIy : 0 ≤ Iy := hnn y1 y2 hy1.le hy2.le
  have hsq : Iz ^ 2 ≤ Ix * Iy := by
    calc Iz ^ 2 ≤ (√Ix * √Iy) ^ 2 := pow_le_pow_left₀ hIz hcs 2
      _ = Ix * Iy := by rw [mul_pow, Real.sq_sqrt hIx, Real.sq_sqrt hIy]
  have hp1 : 0 ≤ (p - 1) ^ 2 := sq_nonneg _
  calc ((p - 1) * Iz) ^ 2 = (p - 1) ^ 2 * Iz ^ 2 := by ring
    _ ≤ (p - 1) ^ 2 * (Ix * Iy) := mul_le_mul_of_nonneg_left hsq hp1
    _ = (p - 1) * Ix * ((p - 1) * Iy) := by ring

lemma G_eq {p a b : ℝ} (hp : 2 ≤ p) (ha : 0 < a) (hb : 0 < b) :
    G p a b = p * a * b * ∫ t in (0:ℝ)..1, D p a b t / a := by
  unfold G
  rw [outer_rep hp, intervalIntegral.integral_div]
  unfold D
  field_simp

end RealPowerCauchySchwarz
