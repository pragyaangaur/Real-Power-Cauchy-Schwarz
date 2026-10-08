import RealPowerCauchySchwarz.Basic

/-!
# The equality cases of Theorem 1

For entrywise nonnegative `v, w ∈ ℝⁿ`, equality holds in
`‖v^p‖ ‖w^p‖ - ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p - ⟨v, w⟩^p`

* for `p > 2` exactly when `v` and `w` are linearly dependent, or each has at most one nonzero
  entry;
* for `p = 2` exactly when `v` and `w` are linearly dependent, or both vanish outside two indices
  `i ≠ j` and `v i w i = v j w j`.

Linear dependence is written as the vanishing of every `2 × 2` minor, `v i w j = v j w i`.
-/

open Real intervalIntegral MeasureTheory Set Finset

namespace RealPowerCauchySchwarz

/-! ## A strict version of the two-by-two estimate -/

/-- Strict Cauchy-Schwarz for interval integrals of continuous functions on `[0,1]`. -/
lemma integral_lt_sqrt_mul {f g h : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (f0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x) (g0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x)
    (h0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ h x) (hfg : ∀ x ∈ Icc (0:ℝ) 1, h x ^ 2 ≤ f x * g x)
    (hlt : ∃ x ∈ Icc (0:ℝ) 1, h x ^ 2 < f x * g x) :
    ∫ x in (0:ℝ)..1, h x < √(∫ x in (0:ℝ)..1, f x) * √(∫ x in (0:ℝ)..1, g x) := by
  have hk : Continuous (fun x => √(f x * g x)) := (hf.mul hg).sqrt
  calc ∫ x in (0:ℝ)..1, h x < ∫ x in (0:ℝ)..1, √(f x * g x) := by
        apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          (by norm_num) hh.continuousOn hk.continuousOn
        · intro x hx
          have hx' : x ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hx
          rw [← Real.sqrt_sq (h0 x hx')]
          exact Real.sqrt_le_sqrt (hfg x hx')
        · obtain ⟨x, hx, hlt⟩ := hlt
          refine ⟨x, hx, ?_⟩
          rw [← Real.sqrt_sq (h0 x hx)]
          exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
    _ ≤ _ := integral_le_sqrt_mul (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
          (hk.intervalIntegrable _ _) f0 g0 (fun x hx => by
            rw [Real.sq_sqrt (mul_nonneg (f0 x hx) (g0 x hx))])

/-- The kernel inequality is strict when `s, t > 0`, `p > 2` and `(x₁, x₂)`, `(y₁, y₂)` are not
proportional in the sense `x₁ y₂ ≠ x₂ y₁`. -/
lemma kernel_sq_lt {p s t x1 x2 y1 y2 z1 z2 : ℝ} (hp : 2 < p) (hs : 0 < s) (ht : 0 < t)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hy1 : 0 < y1) (hy2 : 0 < y2) (hz1' : 0 ≤ z1) (hz2' : 0 ≤ z2)
    (hz1 : z1 ^ 2 ≤ x1 * y1) (hz2 : z2 ^ 2 ≤ x2 * y2) (hne : x1 * y2 ≠ x2 * y1) :
    ((s * z1 + t * z2) ^ (p - 2)) ^ 2
      < (s * x1 + t * x2) ^ (p - 2) * (s * y1 + t * y2) ^ (p - 2) := by
  have h0 : 0 ≤ s * z1 + t * z2 := by positivity
  rw [sq, ← Real.mul_rpow h0 h0, ← Real.mul_rpow (by positivity) (by positivity)]
  apply Real.rpow_lt_rpow (by positivity) _ (by linarith)
  have hprod : (z1 * z2) ^ 2 ≤ (x1 * y2) * (x2 * y1) := by
    rw [mul_pow]
    calc z1 ^ 2 * z2 ^ 2 ≤ (x1 * y1) * (x2 * y2) :=
          mul_le_mul hz1 hz2 (sq_nonneg _) (by positivity)
      _ = (x1 * y2) * (x2 * y1) := by ring
  have hsq : 0 < (x1 * y2 - x2 * y1) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
  have hcross : 2 * (z1 * z2) < x1 * y2 + x2 * y1 := by
    by_contra hge
    push Not at hge
    have hpos : 0 < x1 * y2 + x2 * y1 := by positivity
    have := mul_le_mul hge hge hpos.le (by positivity)
    nlinarith
  have hst : 0 < s * t := mul_pos hs ht
  nlinarith [mul_le_mul_of_nonneg_left hz1 (sq_nonneg s),
    mul_le_mul_of_nonneg_left hz2 (sq_nonneg t), mul_lt_mul_of_pos_left hcross hst]

lemma D_sq_lt {p t x1 x2 y1 y2 z1 z2 : ℝ} (hp : 2 < p) (ht : 0 < t)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hy1 : 0 < y1) (hy2 : 0 < y2) (hz1' : 0 < z1) (hz2' : 0 < z2)
    (hz1 : z1 ^ 2 ≤ x1 * y1) (hz2 : z2 ^ 2 ≤ x2 * y2) (hne : x1 * y2 ≠ x2 * y1) :
    (D p z1 z2 t / z1) ^ 2 < (D p x1 x2 t / x1) * (D p y1 y2 t / y1) := by
  have hp2 : 2 ≤ p := hp.le
  rw [D_div_eq hp2 hz1', D_div_eq hp2 hx1, D_div_eq hp2 hy1]
  have hcont : ∀ a b : ℝ, Continuous (fun s : ℝ => (s * a + t * b) ^ (p - 2)) := fun a b =>
    ((continuous_id.mul continuous_const).add continuous_const).rpow_const
      (fun _ => Or.inr (by linarith))
  have hnn : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ (s * a + t * b) ^ (p - 2) :=
    fun a b ha hb s hs => by have := hs.1; positivity
  have hcs := integral_lt_sqrt_mul (hcont x1 x2) (hcont y1 y2) (hcont z1 z2)
    (hnn x1 x2 hx1.le hx2.le) (hnn y1 y2 hy1.le hy2.le) (hnn z1 z2 hz1'.le hz2'.le)
    (fun s hs => kernel_sq_le hp2 hs.1 ht.le hx1.le hx2.le hy1.le hy2.le hz1'.le hz2'.le hz1 hz2)
    ⟨1, ⟨zero_le_one, le_rfl⟩,
      kernel_sq_lt hp one_pos ht hx1 hx2 hy1 hy2 hz1'.le hz2'.le hz1 hz2 hne⟩
  set Iz := ∫ s in (0:ℝ)..1, (s * z1 + t * z2) ^ (p - 2)
  set Ix := ∫ s in (0:ℝ)..1, (s * x1 + t * x2) ^ (p - 2)
  set Iy := ∫ s in (0:ℝ)..1, (s * y1 + t * y2) ^ (p - 2)
  have hIz : 0 ≤ Iz := intervalIntegral.integral_nonneg (by norm_num) (hnn z1 z2 hz1'.le hz2'.le)
  have hIx : 0 ≤ Ix := intervalIntegral.integral_nonneg (by norm_num) (hnn x1 x2 hx1.le hx2.le)
  have hIy : 0 ≤ Iy := intervalIntegral.integral_nonneg (by norm_num) (hnn y1 y2 hy1.le hy2.le)
  have hsq : Iz ^ 2 < Ix * Iy := by
    calc Iz ^ 2 < (√Ix * √Iy) ^ 2 := pow_lt_pow_left₀ hcs hIz (by norm_num)
      _ = Ix * Iy := by rw [mul_pow, Real.sq_sqrt hIx, Real.sq_sqrt hIy]
  have hp1 : 0 < (p - 1) ^ 2 := by nlinarith
  calc ((p - 1) * Iz) ^ 2 = (p - 1) ^ 2 * Iz ^ 2 := by ring
    _ < (p - 1) ^ 2 * (Ix * Iy) := mul_lt_mul_of_pos_left hsq hp1
    _ = (p - 1) * Ix * ((p - 1) * Iy) := by ring

/-- **Strict two-by-two estimate.** For `p > 2`, positive entries and `x₁ y₂ ≠ x₂ y₁`, the
defect at the geometric means is strictly below the geometric mean of the defects. -/
lemma G_lt_sqrt {p x1 x2 y1 y2 z1 z2 : ℝ} (hp : 2 < p)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hy1 : 0 < y1) (hy2 : 0 < y2) (hz1' : 0 < z1) (hz2' : 0 < z2)
    (hz1 : z1 ^ 2 ≤ x1 * y1) (hz2 : z2 ^ 2 ≤ x2 * y2) (hne : x1 * y2 ≠ x2 * y1) :
    G p z1 z2 < √(G p x1 x2) * √(G p y1 y2) := by
  have hp2 : 2 ≤ p := hp.le
  have hDc : ∀ a b : ℝ, Continuous (fun t => D p a b t / a) := fun a b =>
    (D_continuous hp2).div_const a
  have hDnn : ∀ a b : ℝ, 0 < a → 0 ≤ b → ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ D p a b t / a :=
    fun a b ha hb t ht => div_nonneg (D_nonneg hp2 ha.le hb ht.1) ha.le
  have hcs := integral_lt_sqrt_mul (hDc x1 x2) (hDc y1 y2) (hDc z1 z2)
    (hDnn x1 x2 hx1 hx2.le) (hDnn y1 y2 hy1 hy2.le) (hDnn z1 z2 hz1' hz2'.le)
    (fun t ht => D_sq_le hp2 ht hx1 hx2 hy1 hy2 hz1' hz2' hz1 hz2)
    ⟨1, ⟨zero_le_one, le_rfl⟩, D_sq_lt hp one_pos hx1 hx2 hy1 hy2 hz1' hz2' hz1 hz2 hne⟩
  set Jz := ∫ t in (0:ℝ)..1, D p z1 z2 t / z1
  set Jx := ∫ t in (0:ℝ)..1, D p x1 x2 t / x1
  set Jy := ∫ t in (0:ℝ)..1, D p y1 y2 t / y1
  have hJx : 0 ≤ Jx := intervalIntegral.integral_nonneg (by norm_num) (hDnn x1 x2 hx1 hx2.le)
  have hJy : 0 ≤ Jy := intervalIntegral.integral_nonneg (by norm_num) (hDnn y1 y2 hy1 hy2.le)
  have hp0 : 0 < p := by linarith
  rw [G_eq hp2 hz1' hz2', G_eq hp2 hx1 hx2, G_eq hp2 hy1 hy2]
  rw [Real.sqrt_mul (x := p * x1 * x2) (by positivity),
    Real.sqrt_mul (x := p * y1 * y2) (by positivity)]
  have hc : p * z1 * z2 ≤ √(p * x1 * x2) * √(p * y1 * y2) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    have : (z1 * z2) ^ 2 ≤ (x1 * y1) * (x2 * y2) := by
      rw [mul_pow]; exact mul_le_mul hz1 hz2 (sq_nonneg _) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg p)]
  calc p * z1 * z2 * Jz < p * z1 * z2 * (√Jx * √Jy) :=
        mul_lt_mul_of_pos_left hcs (by positivity)
    _ ≤ √(p * x1 * x2) * √(p * y1 * y2) * (√Jx * √Jy) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = √(p * x1 * x2) * √Jx * (√(p * y1 * y2) * √Jy) := by ring

/-- The defect `G` is positive at positive arguments when `p > 1`. -/
lemma G_pos {p a b : ℝ} (hp : 1 < p) (ha : 0 < a) (hb : 0 < b) : 0 < G p a b := by
  unfold G
  have hab : 0 < a + b := by positivity
  have e : ∀ x : ℝ, 0 < x → x ^ p = x ^ (p - 1) * x := fun x hx => by
    rw [Real.rpow_sub_one hx.ne']; field_simp
  have h1 : a ^ (p - 1) < (a + b) ^ (p - 1) :=
    Real.rpow_lt_rpow ha.le (by linarith) (by linarith)
  have h2 : b ^ (p - 1) < (a + b) ^ (p - 1) :=
    Real.rpow_lt_rpow hb.le (by linarith) (by linarith)
  rw [e a ha, e b hb, e (a + b) hab]
  nlinarith [mul_lt_mul_of_pos_right h1 ha, mul_lt_mul_of_pos_right h2 hb]

end RealPowerCauchySchwarz
