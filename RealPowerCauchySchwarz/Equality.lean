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

/-! ## Splitting off one pair of indices -/

/-- The defect matrix of a sum dominates the piece coming from any two of its indices. -/
lemma pair_psd {ι : Type*} [DecidableEq ι] {p : ℝ} (hp : 2 ≤ p) (s : Finset ι)
    (x y z : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hz : ∀ i, 0 ≤ z i)
    (hxyz : ∀ i, z i ^ 2 ≤ x i * y i) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    PSD2 ((∑ k ∈ s, x k) ^ p - ∑ k ∈ s, x k ^ p - G p (x i) (x j))
      ((∑ k ∈ s, y k) ^ p - ∑ k ∈ s, y k ^ p - G p (y i) (y j))
      ((∑ k ∈ s, z k) ^ p - ∑ k ∈ s, z k ^ p - G p (z i) (z j)) := by
  set r := (s.erase i).erase j with hr
  have hsplit : ∀ f : ι → ℝ, ∑ k ∈ s, f k = f i + (f j + ∑ k ∈ r, f k) := fun f => by
    rw [← Finset.add_sum_erase s f hi,
      ← Finset.add_sum_erase (s.erase i) f (Finset.mem_erase.2 ⟨hij.symm, hj⟩)]
  have hR := sum_psd hp r x y z hx hy hz hxyz
  have hX : 0 ≤ ∑ k ∈ r, x k := Finset.sum_nonneg (fun k _ => hx k)
  have hY : 0 ≤ ∑ k ∈ r, y k := Finset.sum_nonneg (fun k _ => hy k)
  have hZ : 0 ≤ ∑ k ∈ r, z k := Finset.sum_nonneg (fun k _ => hz k)
  have hCSr : (∑ k ∈ r, z k) ^ 2 ≤ (∑ k ∈ r, x k) * ∑ k ∈ r, y k :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul r (fun k _ => hx k) (fun k _ => hy k)
      (fun k _ => hxyz k)
  have hij2 := (show PSD2 (x i) (y i) (z i) from ⟨hx i, hy i, hxyz i⟩).add
    (show PSD2 (x j) (y j) (z j) from ⟨hx j, hy j, hxyz j⟩)
  have hG := G_psd hp (add_nonneg (hx i) (hx j)) hX (add_nonneg (hy i) (hy j)) hY
    (add_nonneg (hz i) (hz j)) hZ hij2.2.2 hCSr
  have hsum := hG.add hR
  have ex := hsplit x
  have ey := hsplit y
  have ez := hsplit z
  have exp := hsplit (fun k => x k ^ p)
  have eyp := hsplit (fun k => y k ^ p)
  have ezp := hsplit (fun k => z k ^ p)
  rw [ex, ey, ez, exp, eyp, ezp]
  convert hsum using 1 <;> unfold G <;> ring_nf

/-! ## The quadratic form that detects equality -/

lemma form_nonneg {α β γ : ℝ} (u u' : ℝ) (h : PSD2 α β γ) :
    0 ≤ u' ^ 2 * α + u ^ 2 * β - 2 * u * u' * γ := by
  obtain ⟨hα, hβ, hγ⟩ := h
  have hA : 0 ≤ u' ^ 2 * α := by positivity
  have hB : 0 ≤ u ^ 2 * β := by positivity
  have hC : (u * u' * γ) ^ 2 ≤ (u' ^ 2 * α) * (u ^ 2 * β) := by
    have : (u * u' * γ) ^ 2 = u ^ 2 * u' ^ 2 * γ ^ 2 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hγ (by positivity : 0 ≤ u ^ 2 * u' ^ 2)]
  by_contra hlt
  push Not at hlt
  have h2 : u' ^ 2 * α + u ^ 2 * β < 2 * (u * u' * γ) := by linarith
  have hS : 0 ≤ u' ^ 2 * α + u ^ 2 * β := by positivity
  have := mul_self_lt_mul_self hS h2
  nlinarith [sq_nonneg (u' ^ 2 * α - u ^ 2 * β)]

lemma form_zero {α β γ u u' : ℝ} (h : PSD2 α β γ) (hu : 0 < u) (hu' : 0 < u')
    (h0 : u' ^ 2 * α + u ^ 2 * β - 2 * u * u' * γ = 0) :
    γ ^ 2 = α * β ∧ u' ^ 2 * α = u ^ 2 * β := by
  obtain ⟨hα, hβ, hγ⟩ := h
  have hsq : (u' ^ 2 * α - u ^ 2 * β) ^ 2 = 4 * u ^ 2 * u' ^ 2 * (γ ^ 2 - α * β) := by
    have hS : u' ^ 2 * α + u ^ 2 * β = 2 * u * u' * γ := by linarith
    calc (u' ^ 2 * α - u ^ 2 * β) ^ 2
        = (u' ^ 2 * α + u ^ 2 * β) ^ 2 - 4 * (u' ^ 2 * α) * (u ^ 2 * β) := by ring
      _ = (2 * u * u' * γ) ^ 2 - 4 * (u' ^ 2 * α) * (u ^ 2 * β) := by rw [hS]
      _ = _ := by ring
  have hle : (u' ^ 2 * α - u ^ 2 * β) ^ 2 ≤ 0 := by
    rw [hsq]
    have : 0 ≤ 4 * u ^ 2 * u' ^ 2 := by positivity
    nlinarith
  have heq : u' ^ 2 * α = u ^ 2 * β := by nlinarith [sq_nonneg (u' ^ 2 * α - u ^ 2 * β)]
  refine ⟨?_, heq⟩
  have huu : 0 < 4 * u ^ 2 * u' ^ 2 := by positivity
  have : 4 * u ^ 2 * u' ^ 2 * (γ ^ 2 - α * β) = 0 := by
    rw [← hsq, heq]; ring
  have := (mul_eq_zero.1 this).resolve_left huu.ne'
  linarith

/-! ## The two sides as sums -/

/-- The left-hand side `‖v^p‖ ‖w^p‖ - ⟨v^p, w^p⟩` written as sums. -/
noncomputable def lhs {n : ℕ} (p : ℝ) (v w : Fin n → ℝ) : ℝ :=
  √(∑ i, (v i ^ p) ^ 2) * √(∑ i, (w i ^ p) ^ 2) - ∑ i, v i ^ p * w i ^ p

/-- The right-hand side `‖v‖^p ‖w‖^p - ⟨v, w⟩^p` written as sums. -/
noncomputable def rhs {n : ℕ} (p : ℝ) (v w : Fin n → ℝ) : ℝ :=
  (√(∑ i, v i ^ 2)) ^ p * (√(∑ i, w i ^ 2)) ^ p - (∑ i, v i * w i) ^ p

theorem lhs_le_rhs {n : ℕ} {p : ℝ} (hp : 2 ≤ p) (v w : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) : lhs p v w ≤ rhs p v w :=
  main_sum n p hp v w hv hw

/-- Equality forces every pair of indices to give a degenerate piece. -/
lemma pair_of_eq {n : ℕ} {p : ℝ} (hp : 2 ≤ p) {v w : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) (hV : 0 < ∑ i, v i ^ 2) (hW : 0 < ∑ i, w i ^ 2)
    (heq : lhs p v w = rhs p v w) {i j : Fin n} (hij : i ≠ j) :
    G p (v i * w i) (v j * w j) ^ 2 = G p (v i ^ 2) (v j ^ 2) * G p (w i ^ 2) (w j ^ 2) ∧
    (∑ k, w k ^ 2) ^ p * G p (v i ^ 2) (v j ^ 2)
      = (∑ k, v k ^ 2) ^ p * G p (w i ^ 2) (w j ^ 2) := by
  unfold lhs rhs at heq
  have e1 : ∀ i, (v i ^ p) ^ 2 = (v i ^ 2) ^ p := fun i => by
    rw [sq, sq, Real.mul_rpow (hv i) (hv i)]
  have e2 : ∀ i, (w i ^ p) ^ 2 = (w i ^ 2) ^ p := fun i => by
    rw [sq, sq, Real.mul_rpow (hw i) (hw i)]
  have e3 : ∀ i, v i ^ p * w i ^ p = (v i * w i) ^ p := fun i =>
    (Real.mul_rpow (hv i) (hw i)).symm
  simp only [e1, e2, e3] at heq
  rw [sqrt_rpow_eq hV.le, sqrt_rpow_eq hW.le] at heq
  have hxyz : ∀ k, (v k * w k) ^ 2 ≤ v k ^ 2 * w k ^ 2 := fun k => by rw [mul_pow]
  have hT := sum_psd hp Finset.univ (fun k => v k ^ 2) (fun k => w k ^ 2) (fun k => v k * w k)
    (fun k => sq_nonneg _) (fun k => sq_nonneg _) (fun k => mul_nonneg (hv k) (hw k)) hxyz
  have hP := pair_psd hp Finset.univ (fun k => v k ^ 2) (fun k => w k ^ 2) (fun k => v k * w k)
    (fun k => sq_nonneg _) (fun k => sq_nonneg _) (fun k => mul_nonneg (hv k) (hw k)) hxyz
    (Finset.mem_univ i) (Finset.mem_univ j) hij
  have hX := G_psd hp (sq_nonneg (v i)) (sq_nonneg (v j)) (sq_nonneg (w i)) (sq_nonneg (w j))
    (mul_nonneg (hv i) (hw i)) (mul_nonneg (hv j) (hw j)) (hxyz i) (hxyz j)
  set P := (∑ k, v k ^ 2) ^ p with hPdef
  set Q := (∑ k, w k ^ 2) ^ p with hQdef
  set a := ∑ k, (v k ^ 2) ^ p
  set b := ∑ k, (w k ^ 2) ^ p
  set d := ∑ k, (v k * w k) ^ p
  set Zp := (∑ k, v k * w k) ^ p
  set X11 := G p (v i ^ 2) (v j ^ 2)
  set X22 := G p (w i ^ 2) (w j ^ 2)
  set X12 := G p (v i * w i) (v j * w j)
  have ha : 0 ≤ a := Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (sq_nonneg _) _)
  have hb : 0 ≤ b := Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (sq_nonneg _) _)
  have hP0 : 0 < P := Real.rpow_pos_of_pos hV _
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hW _
  set u := √P with hu
  set u' := √Q with hu'
  set e := √a with he
  set e' := √b with he'
  have hu0 : 0 < u := Real.sqrt_pos.2 hP0
  have hu'0 : 0 < u' := Real.sqrt_pos.2 hQ0
  have hue : u ^ 2 = P := Real.sq_sqrt hP0.le
  have hue' : u' ^ 2 = Q := Real.sq_sqrt hQ0.le
  have hee : e ^ 2 = a := Real.sq_sqrt ha
  have hee' : e' ^ 2 = b := Real.sq_sqrt hb
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have he'0 : 0 ≤ e' := Real.sqrt_nonneg _
  -- equality in the final step
  have hγ : Zp - d = u * u' - e * e' := by linarith
  obtain ⟨-, -, hT3⟩ := hT
  rw [hγ, ← hue, ← hue', ← hee, ← hee'] at hT3
  have hcross : (u * e' - e * u') ^ 2 = 0 := by
    have : (u * e' - e * u') ^ 2
        = (u * u' - e * e') ^ 2 - (u ^ 2 - e ^ 2) * (u' ^ 2 - e' ^ 2) := by ring
    nlinarith [sq_nonneg (u * e' - e * u')]
  have hcross' : u * e' = e * u' := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hcross
    linarith
  have hformT : u' ^ 2 * (P - a) + u ^ 2 * (Q - b) - 2 * u * u' * (Zp - d) = 0 := by
    rw [hγ, ← hue, ← hue', ← hee, ← hee']
    have : (u' * e - u * e') ^ 2 = 0 := by rw [← hcross]; ring
    nlinarith [this]
  have hfP := form_nonneg u u' hP
  have hfX := form_nonneg u u' hX
  have hformX : u' ^ 2 * X11 + u ^ 2 * X22 - 2 * u * u' * X12 = 0 := by
    have : u' ^ 2 * (P - a) + u ^ 2 * (Q - b) - 2 * u * u' * (Zp - d)
        = (u' ^ 2 * (P - a - X11) + u ^ 2 * (Q - b - X22) - 2 * u * u' * (Zp - d - X12))
          + (u' ^ 2 * X11 + u ^ 2 * X22 - 2 * u * u' * X12) := by ring
    linarith
  obtain ⟨h1, h2⟩ := form_zero hX hu0 hu'0 hformX
  exact ⟨h1, by rw [← hue, ← hue']; exact h2⟩

/-! ## Sufficiency: the equality families -/

lemma zero_rpow_of_pos {p : ℝ} (hp : 0 < p) : (0:ℝ) ^ p = 0 := Real.zero_rpow hp.ne'

/-- Linearly dependent vectors give equality, for every `p > 0`. -/
theorem eq_of_minors {n : ℕ} {p : ℝ} (hp : 0 < p) (v w : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) (hmin : ∀ i j, v i * w j = v j * w i) : lhs p v w = rhs p v w := by
  unfold lhs rhs
  by_cases hz : ∀ i, v i = 0
  · simp [hz, zero_rpow_of_pos hp]
  push Not at hz
  obtain ⟨i0, hi0⟩ := hz
  have hpos : 0 < v i0 := lt_of_le_of_ne (hv i0) (Ne.symm hi0)
  set l := w i0 / v i0 with hl
  have hl0 : 0 ≤ l := div_nonneg (hw i0) (hv i0)
  have hwl : ∀ k, w k = l * v k := fun k => by
    rw [hl]; field_simp; linarith [hmin i0 k]
  simp only [hwl]
  have hpow : ∀ k, (l * v k) ^ p = l ^ p * v k ^ p := fun k => Real.mul_rpow hl0 (hv k)
  simp only [hpow]
  have hlp : 0 ≤ l ^ p := Real.rpow_nonneg hl0 _
  have hA : 0 ≤ ∑ k, (v k ^ p) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hV : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have s1 : ∑ k, (l ^ p * v k ^ p) ^ 2 = (l ^ p) ^ 2 * ∑ k, (v k ^ p) ^ 2 := by
    rw [Finset.mul_sum]; congr 1; ext k; ring
  have s2 : ∑ k, v k ^ p * (l ^ p * v k ^ p) = l ^ p * ∑ k, (v k ^ p) ^ 2 := by
    rw [Finset.mul_sum]; congr 1; ext k; ring
  have s3 : ∑ k, (l * v k) ^ 2 = l ^ 2 * ∑ k, v k ^ 2 := by
    rw [Finset.mul_sum]; congr 1; ext k; ring
  have s4 : ∑ k, v k * (l * v k) = l * ∑ k, v k ^ 2 := by
    rw [Finset.mul_sum]; congr 1; ext k; ring
  rw [s1, s2, s3, s4, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlp, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hl0, Real.mul_rpow hl0 (Real.sqrt_nonneg _), Real.mul_rpow hl0 hV]
  have hsq : √(∑ k, (v k ^ p) ^ 2) * √(∑ k, (v k ^ p) ^ 2) = ∑ k, (v k ^ p) ^ 2 :=
    Real.mul_self_sqrt hA
  have hsq2 : (√(∑ k, v k ^ 2)) ^ p * (√(∑ k, v k ^ 2)) ^ p = (∑ k, v k ^ 2) ^ p := by
    rw [← Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), Real.mul_self_sqrt hV]
  linear_combination (l ^ p) * hsq - (l ^ p) * hsq2

/-- Two vectors each supported on a single, different index give equality. -/
theorem eq_of_single {n : ℕ} {p : ℝ} (hp : 0 < p) (v w : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) {i j : Fin n} (hij : i ≠ j) (hvi : ∀ k, k ≠ i → v k = 0)
    (hwj : ∀ k, k ≠ j → w k = 0) : lhs p v w = rhs p v w := by
  unfold lhs rhs
  have h0 := zero_rpow_of_pos hp
  have s1 : ∑ k, (v k ^ p) ^ 2 = (v i ^ p) ^ 2 :=
    Fintype.sum_eq_single i (fun k hk => by rw [hvi k hk, h0]; ring)
  have s2 : ∑ k, (w k ^ p) ^ 2 = (w j ^ p) ^ 2 :=
    Fintype.sum_eq_single j (fun k hk => by rw [hwj k hk, h0]; ring)
  have s3 : ∑ k, v k ^ p * w k ^ p = 0 := Finset.sum_eq_zero (fun k _ => by
    by_cases hk : k = i
    · subst hk; rw [hwj k hij, h0]; ring
    · rw [hvi k hk, h0]; ring)
  have s4 : ∑ k, v k ^ 2 = v i ^ 2 :=
    Fintype.sum_eq_single i (fun k hk => by rw [hvi k hk]; ring)
  have s5 : ∑ k, w k ^ 2 = w j ^ 2 :=
    Fintype.sum_eq_single j (fun k hk => by rw [hwj k hk]; ring)
  have s6 : ∑ k, v k * w k = 0 := Finset.sum_eq_zero (fun k _ => by
    by_cases hk : k = i
    · subst hk; rw [hwj k hij]; ring
    · rw [hvi k hk]; ring)
  rw [s1, s2, s3, s4, s5, s6, h0, Real.sqrt_sq (Real.rpow_nonneg (hv i) _),
    Real.sqrt_sq (Real.rpow_nonneg (hw j) _), Real.sqrt_sq (hv i), Real.sqrt_sq (hw j)]

/-! ## The case `p > 2` -/

lemma pair_two_lt {n : ℕ} {p : ℝ} (hp : 2 < p) {v w : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) (hV : 0 < ∑ i, v i ^ 2) (hW : 0 < ∑ i, w i ^ 2)
    (heq : lhs p v w = rhs p v w) {i j : Fin n} (hij : i ≠ j) :
    (v i * v j = 0 ↔ w i * w j = 0) ∧ (v i * v j ≠ 0 → v i * w j = v j * w i) := by
  obtain ⟨h1, h2⟩ := pair_of_eq hp.le hv hw hV hW heq hij
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hP0 : 0 < (∑ k, v k ^ 2) ^ p := Real.rpow_pos_of_pos hV _
  have hQ0 : 0 < (∑ k, w k ^ 2) ^ p := Real.rpow_pos_of_pos hW _
  -- `G` at a pair of squares vanishes exactly when the product vanishes
  have Gzero : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (G p (x ^ 2) (y ^ 2) = 0 ↔ x * y = 0) := by
    intro x y hx hy
    constructor
    · intro h
      by_contra hxy
      have hx' : 0 < x := lt_of_le_of_ne hx (by rintro rfl; simp at hxy)
      have hy' : 0 < y := lt_of_le_of_ne hy (by rintro rfl; simp at hxy)
      have := G_pos hp1 (pow_pos hx' 2) (pow_pos hy' 2)
      linarith
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · rw [h]; simpa using G_zero_left hp0
      · rw [h]; simpa using G_zero_right hp0
  have hiff : v i * v j = 0 ↔ w i * w j = 0 := by
    rw [← Gzero _ _ (hv i) (hv j), ← Gzero _ _ (hw i) (hw j)]
    constructor
    · intro h; rw [h, mul_zero] at h2
      exact (mul_eq_zero.1 h2.symm).resolve_left hP0.ne'
    · intro h; rw [h, mul_zero] at h2
      exact (mul_eq_zero.1 h2).resolve_left hQ0.ne'
  refine ⟨hiff, fun hvv => ?_⟩
  have hww : w i * w j ≠ 0 := fun h => hvv (hiff.2 h)
  have pos : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x * y ≠ 0 → 0 < x ∧ 0 < y := fun x y hx hy h =>
    ⟨lt_of_le_of_ne hx (by rintro rfl; simp at h), lt_of_le_of_ne hy (by rintro rfl; simp at h)⟩
  obtain ⟨hvi, hvj⟩ := pos _ _ (hv i) (hv j) hvv
  obtain ⟨hwi, hwj⟩ := pos _ _ (hw i) (hw j) hww
  by_contra hne
  have hne2 : v i ^ 2 * w j ^ 2 ≠ v j ^ 2 * w i ^ 2 := by
    intro h
    apply hne
    have h' : (v i * w j) ^ 2 = (v j * w i) ^ 2 := by rw [mul_pow, mul_pow]; linarith
    exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).1 h'
  have hlt := G_lt_sqrt hp (pow_pos hvi 2) (pow_pos hvj 2) (pow_pos hwi 2) (pow_pos hwj 2)
    (mul_pos hvi hwi) (mul_pos hvj hwj) (by rw [mul_pow]) (by rw [mul_pow]) hne2
  have hX12 : 0 ≤ G p (v i * w i) (v j * w j) :=
    G_nonneg hp1.le (mul_pos hvi hwi).le (mul_pos hvj hwj).le
  have hX11 : 0 ≤ G p (v i ^ 2) (v j ^ 2) := G_nonneg hp1.le (sq_nonneg _) (sq_nonneg _)
  have hX22 : 0 ≤ G p (w i ^ 2) (w j ^ 2) := G_nonneg hp1.le (sq_nonneg _) (sq_nonneg _)
  have : G p (v i * w i) (v j * w j) ^ 2 < G p (v i ^ 2) (v j ^ 2) * G p (w i ^ 2) (w j ^ 2) := by
    calc G p (v i * w i) (v j * w j) ^ 2
        < (√(G p (v i ^ 2) (v j ^ 2)) * √(G p (w i ^ 2) (w j ^ 2))) ^ 2 :=
          pow_lt_pow_left₀ hlt hX12 (by norm_num)
      _ = _ := by rw [mul_pow, Real.sq_sqrt hX11, Real.sq_sqrt hX22]
  linarith

lemma sum_sq_eq_zero {n : ℕ} {v : Fin n → ℝ} (h : ∑ i, v i ^ 2 = 0) : ∀ i, v i = 0 := by
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (v k))).1 h i
    (Finset.mem_univ i)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-- **Equality for `p > 2`.** For real `p > 2` and entrywise nonnegative `v, w`, equality holds in
Theorem 1 if and only if `v` and `w` are linearly dependent, or each of them has at most one
nonzero entry. -/
theorem eq_iff_of_two_lt {n : ℕ} {p : ℝ} (hp : 2 < p) (v w : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) :
    lhs p v w = rhs p v w ↔
      ((∀ i j, v i * w j = v j * w i) ∨
        (∀ i j, i ≠ j → v i * v j = 0 ∧ w i * w j = 0)) := by
  have hp0 : 0 < p := by linarith
  constructor
  · intro heq
    have hV0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have hW0 : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rcases hV0.eq_or_lt with hV | hV
    · left; intro i j; rw [sum_sq_eq_zero hV.symm i, sum_sq_eq_zero hV.symm j]; ring
    rcases hW0.eq_or_lt with hW | hW
    · left; intro i j; rw [sum_sq_eq_zero hW.symm i, sum_sq_eq_zero hW.symm j]; ring
    by_cases hsp : ∀ i j, i ≠ j → v i * v j = 0 ∧ w i * w j = 0
    · exact Or.inr hsp
    left
    push Not at hsp
    obtain ⟨i0, j0, hij, hnz⟩ := hsp
    have hpair := fun {i j : Fin n} (h : i ≠ j) => pair_two_lt hp hv hw hV hW heq h
    have hvv : v i0 * v j0 ≠ 0 := by
      intro h
      exact hnz h ((hpair hij).1.1 h)
    have hww : w i0 * w j0 ≠ 0 := fun h => hvv ((hpair hij).1.2 h)
    have hv0 : v i0 ≠ 0 := left_ne_zero_of_mul hvv
    have hw0 : w i0 ≠ 0 := left_ne_zero_of_mul hww
    have hk : ∀ k, v i0 * w k = v k * w i0 := by
      intro k
      by_cases hki : k = i0
      · rw [hki]
      by_cases hvk : v i0 * v k = 0
      · have hwk := ((hpair (Ne.symm hki)).1).1 hvk
        have hvk' : v k = 0 := (mul_eq_zero.1 hvk).resolve_left hv0
        have hwk' : w k = 0 := (mul_eq_zero.1 hwk).resolve_left hw0
        rw [hvk', hwk']; ring
      · exact (hpair (Ne.symm hki)).2 hvk
    intro k l
    apply mul_left_cancel₀ hv0
    have h1 := hk l
    have h2 := hk k
    calc v i0 * (v k * w l) = v k * (v i0 * w l) := by ring
      _ = v k * (v l * w i0) := by rw [h1]
      _ = v l * (v k * w i0) := by ring
      _ = v l * (v i0 * w k) := by rw [h2]
      _ = v i0 * (v l * w k) := by ring
  · rintro (hmin | hsp)
    · exact eq_of_minors hp0 v w hv hw hmin
    by_cases hmin : ∀ i j, v i * w j = v j * w i
    · exact eq_of_minors hp0 v w hv hw hmin
    push Not at hmin
    obtain ⟨k, l, hkl⟩ := hmin
    have hne : k ≠ l := by rintro rfl; exact hkl rfl
    by_cases h1 : v k * w l ≠ 0
    · have hvk : v k ≠ 0 := left_ne_zero_of_mul h1
      have hwl : w l ≠ 0 := right_ne_zero_of_mul h1
      refine eq_of_single hp0 v w hv hw hne (fun m hm => ?_) (fun m hm => ?_)
      · exact (mul_eq_zero.1 ((hsp k m (Ne.symm hm)).1)).resolve_left hvk
      · exact (mul_eq_zero.1 ((hsp l m (Ne.symm hm)).2)).resolve_left hwl
    · push Not at h1
      have h2 : v l * w k ≠ 0 := by rw [h1] at hkl; exact Ne.symm hkl
      have hvl : v l ≠ 0 := left_ne_zero_of_mul h2
      have hwk : w k ≠ 0 := right_ne_zero_of_mul h2
      refine eq_of_single hp0 v w hv hw (Ne.symm hne) (fun m hm => ?_) (fun m hm => ?_)
      · exact (mul_eq_zero.1 ((hsp l m (Ne.symm hm)).1)).resolve_left hvl
      · exact (mul_eq_zero.1 ((hsp k m (Ne.symm hm)).2)).resolve_left hwk

/-! ## The case `p = 2` -/

lemma G_two (a b : ℝ) : G 2 a b = 2 * a * b := by
  unfold G; simp only [Real.rpow_two]; ring

/-- **Equality for `p = 2`.** For entrywise nonnegative `v, w`, equality holds in Theorem 1 with
`p = 2` if and only if `v` and `w` are linearly dependent, or there are indices `i ≠ j` outside
which both vectors vanish and `v i w i = v j w j`. -/
theorem eq_iff_two {n : ℕ} (v w : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    lhs 2 v w = rhs 2 v w ↔
      ((∀ i j, v i * w j = v j * w i) ∨
        ∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → v k = 0 ∧ w k = 0) ∧ v i * w i = v j * w j) := by
  constructor
  · intro heq
    have hV0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have hW0 : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rcases hV0.eq_or_lt with hV | hV
    · left; intro i j; rw [sum_sq_eq_zero hV.symm i, sum_sq_eq_zero hV.symm j]; ring
    rcases hW0.eq_or_lt with hW | hW
    · left; intro i j; rw [sum_sq_eq_zero hW.symm i, sum_sq_eq_zero hW.symm j]; ring
    by_cases hmin : ∀ i j, v i * w j = v j * w i
    · exact Or.inl hmin
    right
    push Not at hmin
    obtain ⟨i0, j0, hne⟩ := hmin
    have hij : i0 ≠ j0 := by rintro rfl; exact hne rfl
    set V := ∑ k, v k ^ 2 with hVdef
    set W := ∑ k, w k ^ 2 with hWdef
    -- the pairwise relation `W v_k v_l = V w_k w_l`
    have hpair : ∀ k l, k ≠ l → W * (v k * v l) = V * (w k * w l) := by
      intro k l hkl
      have h2 := (pair_of_eq (le_refl 2) hv hw hV hW heq hkl).2
      simp only [G_two, Real.rpow_two] at h2
      have h3 : (W * (v k * v l)) ^ 2 = (V * (w k * w l)) ^ 2 := by nlinarith [h2]
      have hv' : 0 ≤ W * (v k * v l) := by have := hv k; have := hv l; positivity
      have hw' : 0 ≤ V * (w k * w l) := by have := hw k; have := hw l; positivity
      exact (pow_left_inj₀ hv' hw' (by norm_num)).1 h3
    have hd : v i0 * w j0 - v j0 * w i0 ≠ 0 := sub_ne_zero.2 hne
    have hrest : ∀ k, k ≠ i0 → k ≠ j0 → v k = 0 ∧ w k = 0 := by
      intro k hki hkj
      have a1 := hpair i0 k (Ne.symm hki)
      have a2 := hpair j0 k (Ne.symm hkj)
      constructor
      · have : W * v k * (v i0 * w j0 - v j0 * w i0) = 0 := by
          have b1 := hpair i0 j0 hij
          linear_combination (w j0) * a1 - (w i0) * a2 + 0 * b1
        have hWv : W * v k = 0 := (mul_eq_zero.1 this).resolve_right hd
        exact (mul_eq_zero.1 hWv).resolve_left hW.ne'
      · have : V * w k * (v i0 * w j0 - v j0 * w i0) = 0 := by
          linear_combination (v j0) * a1 - (v i0) * a2
        have hVw : V * w k = 0 := (mul_eq_zero.1 this).resolve_right hd
        exact (mul_eq_zero.1 hVw).resolve_left hV.ne'
    refine ⟨i0, j0, hij, hrest, ?_⟩
    have hVs : V = v i0 ^ 2 + v j0 ^ 2 :=
      Fintype.sum_eq_add i0 j0 hij (fun k hk => by rw [(hrest k hk.1 hk.2).1]; ring)
    have hWs : W = w i0 ^ 2 + w j0 ^ 2 :=
      Fintype.sum_eq_add i0 j0 hij (fun k hk => by rw [(hrest k hk.1 hk.2).2]; ring)
    have b1 := hpair i0 j0 hij
    rw [hVs, hWs] at b1
    have : (v i0 * w j0 - v j0 * w i0) * (v i0 * w i0 - v j0 * w j0) = 0 := by
      linear_combination -b1
    have := (mul_eq_zero.1 this).resolve_left hd
    linarith
  · rintro (hmin | ⟨i, j, hij, hrest, hm⟩)
    · exact eq_of_minors two_pos v w hv hw hmin
    unfold lhs rhs
    simp only [Real.rpow_two]
    have sum2 : ∀ f : Fin n → ℝ, (∀ k, k ≠ i → k ≠ j → f k = 0) → ∑ k, f k = f i + f j :=
      fun f hf => Fintype.sum_eq_add i j hij (fun k hk => hf k hk.1 hk.2)
    rw [sum2 (fun k => (v k ^ 2) ^ 2) (fun k h1 h2 => by simp [(hrest k h1 h2).1]),
      sum2 (fun k => (w k ^ 2) ^ 2) (fun k h1 h2 => by simp [(hrest k h1 h2).2]),
      sum2 (fun k => v k ^ 2 * w k ^ 2) (fun k h1 h2 => by simp [(hrest k h1 h2).1]),
      sum2 (fun k => v k ^ 2) (fun k h1 h2 => by simp [(hrest k h1 h2).1]),
      sum2 (fun k => w k ^ 2) (fun k h1 h2 => by simp [(hrest k h1 h2).2]),
      sum2 (fun k => v k * w k) (fun k h1 h2 => by simp [(hrest k h1 h2).1]),
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ← Real.sqrt_mul (by positivity)]
    set X := (v i * w j) ^ 2 + (v j * w i) ^ 2 with hX
    have hprod : ((v i ^ 2) ^ 2 + (v j ^ 2) ^ 2) * ((w i ^ 2) ^ 2 + (w j ^ 2) ^ 2) = X ^ 2 := by
      have hm2 : v i ^ 2 * w i ^ 2 = v j ^ 2 * w j ^ 2 := by
        rw [← mul_pow, ← mul_pow, hm]
      rw [hX]
      linear_combination (v i ^ 2 * w i ^ 2 - v j ^ 2 * w j ^ 2) * hm2
    rw [hprod, Real.sqrt_sq (by positivity), hX]
    linear_combination (v j * w j - v i * w i) * hm

end RealPowerCauchySchwarz
