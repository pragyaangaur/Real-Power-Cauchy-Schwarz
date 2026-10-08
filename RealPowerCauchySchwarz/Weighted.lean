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

/-- The weighted left-hand side `‖v^p‖_ω ‖w^p‖_ω - ⟨v^p, w^p⟩_ω`. -/
noncomputable def wLHS {n : ℕ} (ω : Fin n → ℝ) (p : ℝ) (v w : Fin n → ℝ) : ℝ :=
  √(∑ i, ω i * (v i ^ p) ^ 2) * √(∑ i, ω i * (w i ^ p) ^ 2) - ∑ i, ω i * (v i ^ p * w i ^ p)

/-- The weighted right-hand side `‖v‖_ω^p ‖w‖_ω^p - ⟨v, w⟩_ω^p`. -/
noncomputable def wRHS {n : ℕ} (ω : Fin n → ℝ) (p : ℝ) (v w : Fin n → ℝ) : ℝ :=
  (√(∑ i, ω i * v i ^ 2)) ^ p * (√(∑ i, ω i * w i ^ 2)) ^ p - (∑ i, ω i * (v i * w i)) ^ p

/-- The extra positive semidefinite term `(ω^(p-1) - t) ω Q` coming from a weight `ω` whose
`(p-1)`-st power is at least `t`. -/
lemma psd2_extra {p t ω x y : ℝ} (hω : 0 < ω) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : t ≤ ω ^ (p - 1)) :
    PSD2 ((ω * x ^ 2) ^ p - t * (ω * (x ^ p) ^ 2)) ((ω * y ^ 2) ^ p - t * (ω * (y ^ p) ^ 2))
      ((ω * (x * y)) ^ p - t * (ω * (x ^ p * y ^ p))) := by
  have key : ∀ z : ℝ, 0 ≤ z → (ω * z) ^ p = ω ^ (p - 1) * (ω * z ^ p) := fun z hz => by
    rw [Real.mul_rpow hω.le hz, ← mul_assoc, ← Real.rpow_add_one hω.ne']
    ring_nf
  have hx2 : (x ^ 2) ^ p = (x ^ p) ^ 2 := by
    rw [sq, sq, Real.mul_rpow hx hx]
  have hy2 : (y ^ 2) ^ p = (y ^ p) ^ 2 := by
    rw [sq, sq, Real.mul_rpow hy hy]
  rw [key _ (sq_nonneg x), key _ (sq_nonneg y), key _ (mul_nonneg hx hy), hx2, hy2,
    Real.mul_rpow hx hy]
  have hc : 0 ≤ (ω ^ (p - 1) - t) * ω := mul_nonneg (by linarith) hω.le
  have := (psd2_pow (p := p) (x := x) (y := y)).smul hc
  convert this using 1 <;> ring

lemma sqrt_rpow_mul {X Y p : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (√X) ^ p * (√Y) ^ p = (X * Y) ^ (p / 2) := by
  rw [← Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ← Real.sqrt_mul hX,
    Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- **Sufficiency.** If every product of two different weights is at least one, the weighted
inequality holds for every real `p ≥ 2`. -/
theorem weighted_of_pairwise {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i)
    (hpair : ∀ i j, i ≠ j → 1 ≤ ω i * ω j) (p : ℝ) (hp : 2 ≤ p) (v w : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) : wLHS ω p v w ≤ wRHS ω p v w := by
  classical
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  -- the generic final step, comparing two defects
  unfold wLHS wRHS
  by_cases hall : ∀ i, 1 ≤ ω i
  · -- every weight is at least one
    have hS := sum_psd hp Finset.univ (fun i => ω i * v i ^ 2) (fun i => ω i * w i ^ 2)
      (fun i => ω i * (v i * w i)) (fun i => by have := hω i; positivity)
      (fun i => by have := hω i; positivity)
      (fun i => by have := hω i; have := hv i; have := hw i; positivity)
      (fun i => le_of_eq (by ring))
    have hE := PSD2.sum Finset.univ _ _ _ (fun i _ => psd2_extra (t := 1) (hω i) (hv i) (hw i)
      (Real.one_le_rpow (hall i) (by linarith)))
    have hT := hS.add hE
    rw [sqrt_rpow_eq (Finset.sum_nonneg (fun i _ => by have := hω i; positivity)),
      sqrt_rpow_eq (Finset.sum_nonneg (fun i _ => by have := hω i; positivity))]
    apply final_step (Finset.sum_nonneg (fun i _ => by have := hω i; positivity))
      (Finset.sum_nonneg (fun i _ => by have := hω i; positivity))
    convert hT using 1 <;> simp only [Finset.sum_sub_distrib, one_mul] <;> ring
  · -- exactly one weight is below one
    push Not at hall
    obtain ⟨k, hk⟩ := hall
    have hωk := hω k
    have hrest : ∀ j, j ≠ k → 1 / ω k ≤ ω j := fun j hj => by
      rw [div_le_iff₀ hωk]; linarith [hpair j k hj]
    set t := (1 / ω k) ^ (p - 1) with ht
    have ht1 : 1 ≤ t := Real.one_le_rpow (by rw [le_div_iff₀ hωk]; linarith) (by linarith)
    have ht0 : 0 < t := by linarith
    set s := Finset.univ.erase k with hs
    -- split every sum into the index `k` and the rest
    have split : ∀ f : Fin n → ℝ, ∑ i, f i = f k + ∑ i ∈ s, f i := fun f =>
      (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
    set a := √(ω k) * v k with ha
    set c := √(ω k) * w k with hc
    have hsq : √(ω k) ^ 2 = ω k := Real.sq_sqrt hωk.le
    set b2 := ∑ i ∈ s, ω i * v i ^ 2 with hb2
    set d2 := ∑ i ∈ s, ω i * w i ^ 2 with hd2
    set e := ∑ i ∈ s, ω i * (v i * w i) with he
    have hb20 : 0 ≤ b2 := Finset.sum_nonneg (fun i _ => by have := hω i; positivity)
    have hd20 : 0 ≤ d2 := Finset.sum_nonneg (fun i _ => by have := hω i; positivity)
    have he0 : 0 ≤ e := Finset.sum_nonneg (fun i _ => by
      have := hω i; have := hv i; have := hw i; positivity)
    have hCS : e ^ 2 ≤ b2 * d2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => by have := hω i; positivity)
        (fun i _ => by have := hω i; positivity) (fun i _ => by
          have := hω i; rw [mul_pow, mul_pow]; nlinarith [sq_nonneg (ω i)])
    set b := √b2 with hb
    set d := √d2 with hd
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hd0 : 0 ≤ d := Real.sqrt_nonneg _
    have hbb : b ^ 2 = b2 := Real.sq_sqrt hb20
    have hdd : d ^ 2 = d2 := Real.sq_sqrt hd20
    have heBD : e ≤ b * d := by
      rw [← Real.sqrt_sq he0, hb, hd, ← Real.sqrt_mul hb20]
      exact Real.sqrt_le_sqrt hCS
    have ha0 : 0 ≤ a := by have := hv k; positivity
    have hc0 : 0 ≤ c := by have := hw k; positivity
    -- the right-hand side
    have hR1 : ∑ i, ω i * v i ^ 2 = a ^ 2 + b ^ 2 := by
      rw [split, hbb, ha, mul_pow, hsq]
    have hR2 : ∑ i, ω i * w i ^ 2 = c ^ 2 + d ^ 2 := by
      rw [split, hdd, hc, mul_pow, hsq]
    have hR3 : ∑ i, ω i * (v i * w i) = a * c + e := by
      rw [split, ha, hc]
      have : √(ω k) * v k * (√(ω k) * w k) = √(ω k) ^ 2 * (v k * w k) := by ring
      rw [this, hsq]
    rw [hR1, hR2, hR3, sqrt_rpow_mul (by positivity) (by positivity)]
    -- the rank-one part, written with `α = a^p`, `γ = c^p`
    set α := a ^ p with hα
    set γ := c ^ p with hγ
    have hα0 : 0 ≤ α := by positivity
    have hγ0 : 0 ≤ γ := by positivity
    have hkey : ∀ x : ℝ, 0 ≤ x → ω k * (x ^ p) ^ 2 = t * (√(ω k) * x) ^ p * (√(ω k) * x) ^ p := by
      intro x hx
      rw [ht, Real.mul_rpow (Real.sqrt_nonneg _) hx]
      have hs : √(ω k) ^ p * √(ω k) ^ p = ω k ^ p := by
        rw [← Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
          Real.mul_self_sqrt hωk.le]
      have h1 : (1 / ω k) ^ (p - 1) * ω k ^ p = ω k := by
        rw [Real.div_rpow zero_le_one hωk.le, Real.one_rpow, Real.rpow_sub_one hωk.ne']
        field_simp
      calc ω k * (x ^ p) ^ 2 = ((1 / ω k) ^ (p - 1) * ω k ^ p) * (x ^ p) ^ 2 := by rw [h1]
        _ = (1 / ω k) ^ (p - 1) * (√(ω k) ^ p * √(ω k) ^ p) * (x ^ p) ^ 2 := by rw [hs]
        _ = _ := by ring
    have hkv := hkey (v k) (hv k)
    have hkw := hkey (w k) (hw k)
    have hkvw : ω k * (v k ^ p * w k ^ p) = t * (α * γ) := by
      rw [hα, hγ, ha, hc, Real.mul_rpow (Real.sqrt_nonneg _) (hv k),
        Real.mul_rpow (Real.sqrt_nonneg _) (hw k)]
      have hs : √(ω k) ^ p * √(ω k) ^ p = ω k ^ p := by
        rw [← Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
          Real.mul_self_sqrt hωk.le]
      have h1 : (1 / ω k) ^ (p - 1) * ω k ^ p = ω k := by
        rw [Real.div_rpow zero_le_one hωk.le, Real.one_rpow, Real.rpow_sub_one hωk.ne']
        field_simp
      calc ω k * (v k ^ p * w k ^ p) = ((1 / ω k) ^ (p - 1) * ω k ^ p) * (v k ^ p * w k ^ p) := by
            rw [h1]
        _ = (1 / ω k) ^ (p - 1) * (√(ω k) ^ p * √(ω k) ^ p) * (v k ^ p * w k ^ p) := by rw [hs]
        _ = _ := by ring
    -- the rest is dominated by `R^{∘p} / t`
    have hS := sum_psd hp s (fun i => ω i * v i ^ 2) (fun i => ω i * w i ^ 2)
      (fun i => ω i * (v i * w i)) (fun i => by have := hω i; positivity)
      (fun i => by have := hω i; positivity)
      (fun i => by have := hω i; have := hv i; have := hw i; positivity)
      (fun i => le_of_eq (by ring))
    have hE := PSD2.sum s _ _ _ (fun i hi => psd2_extra (t := t) (hω i) (hv i) (hw i) (by
      rw [ht]
      exact Real.rpow_le_rpow (by positivity) (hrest i (Finset.ne_of_mem_erase hi))
        (by linarith)))
    have hT := (hS.add hE).smul (show 0 ≤ 1 / t by positivity)
    rw [← hb2, ← hd2, ← he] at hT
    set B := b ^ p with hB
    set D := d ^ p with hD
    have hB0 : 0 ≤ B := by positivity
    have hD0 : 0 ≤ D := by positivity
    have hBB : B ^ 2 = b2 ^ p := by
      rw [hB, ← hbb, sq, sq, Real.mul_rpow hb0 hb0]
    have hDD : D ^ 2 = d2 ^ p := by
      rw [hD, ← hdd, sq, sq, Real.mul_rpow hd0 hd0]
    -- compare the left-hand side with the defect of `t·(rank one) + R^{∘p}/t`
    have hmono : √(∑ i, ω i * (v i ^ p) ^ 2) * √(∑ i, ω i * (w i ^ p) ^ 2)
          - ∑ i, ω i * (v i ^ p * w i ^ p)
        ≤ √(t * α ^ 2 + B ^ 2 / t) * √(t * γ ^ 2 + D ^ 2 / t) - (t * (α * γ) + e ^ p / t) := by
      apply final_step (Finset.sum_nonneg (fun i _ => by have := hω i; positivity))
        (Finset.sum_nonneg (fun i _ => by have := hω i; positivity))
      rw [split, split, split (fun i => ω i * (v i ^ p * w i ^ p)), hkv, hkw, hkvw, hBB, hDD]
      convert hT using 1
      · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]; field_simp; ring
      · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]; field_simp; ring
      · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]; field_simp; ring
    have heBDp : e ^ p ≤ B * D := by
      rw [hB, hD, ← Real.mul_rpow hb0 hd0]
      exact Real.rpow_le_rpow he0 heBD (by linarith)
    have hsup := sup_bound ht1 hα0 hγ0 hB0 hD0 heBDp
    have h2 := two_dim hp ha0 hb0 hc0 hd0
    have hm := merge hp1 (mul_nonneg ha0 hc0) he0 heBD
    have hαD : α * D = (a * d) ^ p := by rw [hα, hD, Real.mul_rpow ha0 hd0]
    have hγB : γ * B = (b * c) ^ p := by rw [hγ, hB, Real.mul_rpow hb0 hc0]; ring
    have hBD : B * D = (b * d) ^ p := by rw [hB, hD, Real.mul_rpow hb0 hd0]
    rw [hαD, hγB, hBD] at hsup
    linarith

/-- **Necessity.** If two different weights have product below one, the weighted inequality fails
for every `p > 1` at a pair of standard basis vectors. -/
theorem not_weighted_of_lt {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) {i j : Fin n}
    (hij : i ≠ j) (hlt : ω i * ω j < 1) {p : ℝ} (hp : 1 < p) :
    wRHS ω p (Pi.single i 1) (Pi.single j 1) < wLHS ω p (Pi.single i 1) (Pi.single j 1) := by
  classical
  have hp0 : p ≠ 0 := by linarith
  unfold wLHS wRHS
  have hzero : (0:ℝ) ^ p = 0 := Real.zero_rpow hp0
  simp only [Pi.single_apply]
  simp [hij.symm, hzero]
  have hi := hω i
  have hj := hω j
  rw [← Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ← Real.sqrt_mul hi.le]
  have h0 : 0 < √(ω i * ω j) := Real.sqrt_pos.2 (by positivity)
  have h1 : √(ω i * ω j) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hlt
  calc √(ω i * ω j) ^ p < √(ω i * ω j) ^ (1:ℝ) :=
        Real.rpow_lt_rpow_of_exponent_gt h0 h1 hp
    _ = √(ω i * ω j) := Real.rpow_one _

/-- **The weighted inequality, characterised.** For positive weights and every real `p ≥ 2`, the
weighted inequality holds for all entrywise nonnegative `v, w` if and only if `ω i * ω j ≥ 1`
for all `i ≠ j`. The condition does not depend on `p`. -/
theorem weighted_iff {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (p : ℝ) (hp : 2 ≤ p) :
    (∀ v w : Fin n → ℝ, (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ w i) → wLHS ω p v w ≤ wRHS ω p v w) ↔
      ∀ i j, i ≠ j → 1 ≤ ω i * ω j := by
  constructor
  · intro h i j hij
    by_contra hlt
    push Not at hlt
    have := not_weighted_of_lt ω hω hij hlt (by linarith : 1 < p)
    have h' := h (Pi.single i 1) (Pi.single j 1)
      (fun k => by by_cases hk : k = i <;> simp [hk])
      (fun k => by by_cases hk : k = j <;> simp [hk])
    linarith
  · intro hpair v w hv hw
    exact weighted_of_pairwise ω hω hpair p hp v w hv hw

end RealPowerCauchySchwarz
