import RealPowerCauchySchwarz.Basic

/-!
# The weighted inequality

For positive weights `ω` and real `p ≥ 2`, the inequality
`‖v^p‖_ω ‖w^p‖_ω - ⟨v^p, w^p⟩_ω ≤ ‖v‖_ω^p ‖w‖_ω^p - ⟨v, w⟩_ω^p`,
with every norm and inner product taken for the same weighted counting measure, holds for all
entrywise nonnegative `v, w` exactly when `ω i * ω j ≥ 1` for all `i ≠ j`.
-/

open Real Finset

namespace RealPowerCauchySchwarz

/-- `(a + c) ^ r - c ^ r` is nondecreasing in `c ≥ 0` when `r ≥ 1` and `a ≥ 0`. -/
lemma mono_diff {r a c c' : ℝ} (hr : 1 ≤ r) (ha : 0 ≤ a) (hc : 0 ≤ c) (hcc : c ≤ c') :
    (a + c) ^ r - c ^ r ≤ (a + c') ^ r - c' ^ r := by
  have hp : 2 ≤ r + 1 := by linarith
  have h1 := inner_rep (p := r + 1) (a := a) (c := c) hp
  have h2 := inner_rep (p := r + 1) (a := a) (c := c') hp
  simp only [add_sub_cancel_right] at h1 h2
  rw [h1, h2]
  apply mul_le_mul_of_nonneg_left _ (by nlinarith)
  apply intervalIntegral.integral_mono_on (by norm_num) (kernel_integrable hp a c)
    (kernel_integrable hp a c')
  intro s hs
  have := hs.1
  exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)

lemma PSD2.smul {α β γ c : ℝ} (h : PSD2 α β γ) (hc : 0 ≤ c) : PSD2 (c * α) (c * β) (c * γ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by positivity, by positivity, ?_⟩
  have : (c * γ) ^ 2 = c ^ 2 * γ ^ 2 := by ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg c)]

lemma PSD2.zero : PSD2 0 0 0 := ⟨le_rfl, le_rfl, by norm_num⟩

lemma PSD2.sum {ι : Type*} (s : Finset ι) (α β γ : ι → ℝ) (h : ∀ i ∈ s, PSD2 (α i) (β i) (γ i)) :
    PSD2 (∑ i ∈ s, α i) (∑ i ∈ s, β i) (∑ i ∈ s, γ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PSD2.zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The rank-one matrix of entrywise `p`-th powers is positive semidefinite. -/
lemma psd2_pow {p x y : ℝ} :
    PSD2 ((x ^ p) ^ 2) ((y ^ p) ^ 2) (x ^ p * y ^ p) :=
  ⟨sq_nonneg _, sq_nonneg _, by rw [mul_pow]⟩

/-- The supremum computation. For a rank-one matrix with entries `α², αγ, γ²` and a matrix
with diagonal `B², D²` and off-diagonal `ε ≤ B D`, the defect of `t·(first) + (second)/t`
is at most `αD + γB - 2√(αD·γB) + (BD - ε)` whenever `t ≥ 1`. -/
lemma sup_bound {t α γ B D ε : ℝ} (ht : 1 ≤ t) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hε : ε ≤ B * D) :
    √(t * α ^ 2 + B ^ 2 / t) * √(t * γ ^ 2 + D ^ 2 / t) - t * (α * γ) - ε / t
      ≤ α * D + γ * B - 2 * √(α * D * (γ * B)) + (B * D - ε) := by
  have ht0 : 0 < t := by linarith
  set g := √(α * D * (γ * B)) with hg
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hg2 : g ^ 2 = α * D * (γ * B) := Real.sq_sqrt (by positivity)
  set m := t * (α * γ) + B * D / t with hm
  set s := α * D + γ * B with hs
  have hm0 : 0 ≤ m := by positivity
  -- `m ≥ 2 g` by the arithmetic-geometric mean inequality
  have hm2 : (2 * g) ^ 2 ≤ m ^ 2 := by
    have : m ^ 2 - (2 * g) ^ 2 = (t * (α * γ) - B * D / t) ^ 2 := by
      rw [hm, mul_pow, hg2]; field_simp; ring
    nlinarith [sq_nonneg (t * (α * γ) - B * D / t)]
  have hmg : 2 * g ≤ m := by nlinarith
  have hs2 : (2 * g) ^ 2 ≤ s ^ 2 := by
    rw [mul_pow, hg2, hs]; nlinarith [sq_nonneg (α * D - γ * B)]
  have hsg : 2 * g ≤ s := by
    have : 0 ≤ s := by positivity
    nlinarith
  have hprod : (t * α ^ 2 + B ^ 2 / t) * (t * γ ^ 2 + D ^ 2 / t)
      = m ^ 2 + (α * D - γ * B) ^ 2 := by
    rw [hm]; field_simp; ring
  rw [← Real.sqrt_mul (by positivity), hprod]
  have hroot : √(m ^ 2 + (α * D - γ * B) ^ 2) ≤ m + s - 2 * g := by
    rw [Real.sqrt_le_left (by linarith)]
    have : s ^ 2 = (α * D - γ * B) ^ 2 + 4 * g ^ 2 := by rw [hs, hg2]; ring
    nlinarith [mul_nonneg (sub_nonneg.2 hsg) (sub_nonneg.2 hmg)]
  have hBD : (B * D - ε) / t ≤ B * D - ε := by
    rw [div_le_iff₀ ht0]; nlinarith
  have e : t * (α * γ) + ε / t = m - (B * D - ε) / t := by rw [hm]; field_simp; ring
  linarith

/-- The two-dimensional estimate behind the weighted inequality:
`(ad)^p + (bc)^p - 2 √((ad)^p (bc)^p) ≤ ((a² + b²)(c² + d²))^{p/2} - (ac + bd)^p`. -/
lemma two_dim {p a b c d : ℝ} (hp : 2 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (a * d) ^ p + (b * c) ^ p - 2 * √((a * d) ^ p * (b * c) ^ p)
      ≤ ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) ^ (p / 2) - (a * c + b * d) ^ p := by
  set X := a * d with hX
  set Y := b * c with hY
  set S := a * c + b * d with hS
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hq : 1 ≤ p / 2 := by linarith
  have hp0 : 0 < p := by linarith
  have hlag : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (X - Y) ^ 2 + S ^ 2 := by
    rw [hX, hY, hS]; ring
  have hS4 : 4 * (X * Y) ≤ S ^ 2 := by
    rw [hX, hY, hS]; nlinarith [sq_nonneg (a * c - b * d)]
  have hmono := mono_diff hq (sq_nonneg (X - Y)) (by positivity) hS4
  have hsq : ∀ z : ℝ, 0 ≤ z → (z ^ 2) ^ (p / 2) = z ^ p := fun z hz => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz]; norm_num; ring_nf
  have h4 : (X - Y) ^ 2 + 4 * (X * Y) = (X + Y) ^ 2 := by ring
  rw [h4, hsq _ (by positivity)] at hmono
  rw [hlag, ← hsq S hS0]
  -- the geometric mean `g = √(XY)`
  set g := √(X * Y) with hg
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hgg : g * g = X * Y := Real.mul_self_sqrt (by positivity)
  have h4g : (4 * (X * Y)) ^ (p / 2) = 2 ^ p * g ^ p := by
    rw [← hgg, show 4 * (g * g) = (2 * g) ^ 2 by ring, hsq _ (by positivity),
      Real.mul_rpow (by norm_num) hg0]
  have hroot : √(X ^ p * Y ^ p) = g ^ p := by
    rw [← Real.mul_rpow hX0 hY0, hg, sqrt_rpow_eq (by positivity)]
  rw [h4g] at hmono
  rw [hroot]
  -- superadditivity defect at the geometric mean
  have hG := G_psd hp hX0 hY0 hY0 hX0 hg0 hg0 (by nlinarith) (by nlinarith)
  obtain ⟨hGx, -, hGz⟩ := hG
  have hcomm : G p Y X = G p X Y := by unfold G; ring_nf
  rw [hcomm] at hGz
  have hGg : G p g g ≤ G p X Y := by
    have h0 : 0 ≤ G p g g := G_nonneg (by linarith) hg0 hg0
    nlinarith
  have hgg2 : (g + g) ^ p = 2 ^ p * g ^ p := by
    rw [show g + g = 2 * g by ring, Real.mul_rpow (by norm_num) hg0]
  unfold G at hGg
  rw [hgg2] at hGg
  linarith

/-- Merging step: `(A + B)^p - (A + e)^p ≥ B^p - e^p` for `0 ≤ e ≤ B`, `A ≥ 0`, `p ≥ 1`. -/
lemma merge {p A B e : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (he : 0 ≤ e) (heB : e ≤ B) :
    B ^ p - e ^ p ≤ (A + B) ^ p - (A + e) ^ p := by
  have := mono_diff hp (sub_nonneg.2 heB) he (show e ≤ A + e by linarith)
  have e1 : B - e + e = B := by ring
  have e2 : B - e + (A + e) = A + B := by ring
  rw [e1, e2] at this
  exact this

end RealPowerCauchySchwarz
