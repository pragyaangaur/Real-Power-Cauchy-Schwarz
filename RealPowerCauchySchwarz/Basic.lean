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

/-- The key two-by-two estimate: the defect at geometric means is at most the geometric
mean of the defects. -/
lemma G_le_sqrt {p x1 x2 y1 y2 z1 z2 : ℝ} (hp : 2 ≤ p)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hy1 : 0 < y1) (hy2 : 0 < y2) (hz1' : 0 < z1) (hz2' : 0 < z2)
    (hz1 : z1 ^ 2 ≤ x1 * y1) (hz2 : z2 ^ 2 ≤ x2 * y2) :
    G p z1 z2 ≤ √(G p x1 x2) * √(G p y1 y2) := by
  have hDint : ∀ a b : ℝ, IntervalIntegrable (fun t => D p a b t / a) volume 0 1 :=
    fun a b => ((D_continuous hp).div_const a).intervalIntegrable _ _
  have hDnn : ∀ a b : ℝ, 0 < a → 0 ≤ b → ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ D p a b t / a :=
    fun a b ha hb t ht => div_nonneg (D_nonneg hp ha.le hb ht.1) ha.le
  have hcs := integral_le_sqrt_mul (hDint x1 x2) (hDint y1 y2) (hDint z1 z2)
    (hDnn x1 x2 hx1 hx2.le) (hDnn y1 y2 hy1 hy2.le)
    (fun t ht => D_sq_le hp ht hx1 hx2 hy1 hy2 hz1' hz2' hz1 hz2)
  set Jz := ∫ t in (0:ℝ)..1, D p z1 z2 t / z1
  set Jx := ∫ t in (0:ℝ)..1, D p x1 x2 t / x1
  set Jy := ∫ t in (0:ℝ)..1, D p y1 y2 t / y1
  have hJx : 0 ≤ Jx := intervalIntegral.integral_nonneg (by norm_num) (hDnn x1 x2 hx1 hx2.le)
  have hJy : 0 ≤ Jy := intervalIntegral.integral_nonneg (by norm_num) (hDnn y1 y2 hy1 hy2.le)
  have hp0 : 0 < p := by linarith
  rw [G_eq hp hz1' hz2', G_eq hp hx1 hx2, G_eq hp hy1 hy2]
  rw [Real.sqrt_mul (x := p * x1 * x2) (by positivity),
    Real.sqrt_mul (x := p * y1 * y2) (by positivity)]
  have hc : p * z1 * z2 ≤ √(p * x1 * x2) * √(p * y1 * y2) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    have : (z1 * z2) ^ 2 ≤ (x1 * y1) * (x2 * y2) := by
      rw [mul_pow]; exact mul_le_mul hz1 hz2 (sq_nonneg _) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg p)]
  calc p * z1 * z2 * Jz ≤ p * z1 * z2 * (√Jx * √Jy) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ √(p * x1 * x2) * √(p * y1 * y2) * (√Jx * √Jy) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = √(p * x1 * x2) * √Jx * (√(p * y1 * y2) * √Jy) := by ring

lemma G_nonneg {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ G p a b := by
  unfold G
  have := Real.add_rpow_le_rpow_add ha hb hp
  linarith

lemma G_zero_left {p b : ℝ} (hp : 0 < p) : G p 0 b = 0 := by
  unfold G; simp [Real.zero_rpow hp.ne']

lemma G_zero_right {p a : ℝ} (hp : 0 < p) : G p a 0 = 0 := by
  unfold G; simp [Real.zero_rpow hp.ne']

/-- A real symmetric `2 × 2` matrix `[[α, γ], [γ, β]]` is positive semidefinite exactly when
`0 ≤ α`, `0 ≤ β` and `γ ^ 2 ≤ α β`. We use this elementary description. -/
def PSD2 (α β γ : ℝ) : Prop := 0 ≤ α ∧ 0 ≤ β ∧ γ ^ 2 ≤ α * β

lemma PSD2.add {α β γ α' β' γ' : ℝ} (h : PSD2 α β γ) (h' : PSD2 α' β' γ') :
    PSD2 (α + α') (β + β') (γ + γ') := by
  obtain ⟨ha, hb, hc⟩ := h
  obtain ⟨ha', hb', hc'⟩ := h'
  refine ⟨by linarith, by linarith, ?_⟩
  have hprod : (γ * γ') ^ 2 ≤ (α * β') * (α' * β) := by
    rw [mul_pow]
    calc γ ^ 2 * γ' ^ 2 ≤ (α * β) * (α' * β') :=
          mul_le_mul hc hc' (sq_nonneg _) (by positivity)
      _ = (α * β') * (α' * β) := by ring
  have hcross : 2 * (γ * γ') ≤ α * β' + α' * β := by
    by_contra hlt
    push Not at hlt
    have hS : 0 ≤ α * β' + α' * β := by positivity
    have hT := mul_self_lt_mul_self hS hlt
    nlinarith [sq_nonneg (α * β' - α' * β)]
  nlinarith

/-- Lemma 1 of the writeup in the form used: superadditivity of the entrywise `p`-th power for
two nonnegative `2 × 2` positive semidefinite matrices `[[x1, z1], [z1, y1]]` and
`[[x2, z2], [z2, y2]]`. -/
lemma G_psd {p x1 x2 y1 y2 z1 z2 : ℝ} (hp : 2 ≤ p)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hz1' : 0 ≤ z1) (hz2' : 0 ≤ z2)
    (hz1 : z1 ^ 2 ≤ x1 * y1) (hz2 : z2 ^ 2 ≤ x2 * y2) :
    PSD2 (G p x1 x2) (G p y1 y2) (G p z1 z2) := by
  have hp1 : (1:ℝ) ≤ p := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  refine ⟨G_nonneg hp1 hx1 hx2, G_nonneg hp1 hy1 hy2, ?_⟩
  have hxy : 0 ≤ G p x1 x2 * G p y1 y2 :=
    mul_nonneg (G_nonneg hp1 hx1 hx2) (G_nonneg hp1 hy1 hy2)
  rcases hz1'.eq_or_lt with h1 | h1
  · rw [← h1, G_zero_left hp0]; simpa using hxy
  rcases hz2'.eq_or_lt with h2 | h2
  · rw [← h2, G_zero_right hp0]; simpa using hxy
  have pos : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 < z → z ^ 2 ≤ x * y → 0 < x ∧ 0 < y := by
    intro x y z hx hy hz h
    have hxy : 0 < x * y := lt_of_lt_of_le (by positivity) h
    refine ⟨lt_of_le_of_ne hx ?_, lt_of_le_of_ne hy ?_⟩
    · rintro rfl; simp at hxy
    · rintro rfl; simp at hxy
  obtain ⟨hx1p, hy1p⟩ := pos x1 y1 z1 hx1 hy1 h1 hz1
  obtain ⟨hx2p, hy2p⟩ := pos x2 y2 z2 hx2 hy2 h2 hz2
  have key := G_le_sqrt hp hx1p hx2p hy1p hy2p h1 h2 hz1 hz2
  calc G p z1 z2 ^ 2 ≤ (√(G p x1 x2) * √(G p y1 y2)) ^ 2 :=
        pow_le_pow_left₀ (G_nonneg hp1 h1.le h2.le) key 2
    _ = G p x1 x2 * G p y1 y2 := by
        rw [mul_pow, Real.sq_sqrt (G_nonneg hp1 hx1 hx2), Real.sq_sqrt (G_nonneg hp1 hy1 hy2)]

/-- Repeated application of Lemma 1: for rank-one matrices `[[x i, z i], [z i, y i]]` with
`z i ^ 2 ≤ x i * y i`, the matrix `(∑ A_i)^{∘p} - ∑ A_i^{∘p}` is positive semidefinite. -/
lemma sum_psd {ι : Type*} {p : ℝ} (hp : 2 ≤ p) (s : Finset ι) (x y z : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hz : ∀ i, 0 ≤ z i)
    (hxyz : ∀ i, z i ^ 2 ≤ x i * y i) :
    PSD2 ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ((∑ i ∈ s, y i) ^ p - ∑ i ∈ s, y i ^ p)
      ((∑ i ∈ s, z i) ^ p - ∑ i ∈ s, z i ^ p) := by
  have hp0 : p ≠ 0 := by linarith
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_, ?_⟩ <;> simp [Real.zero_rpow hp0]
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have hX : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg (fun i _ => hx i)
    have hY : 0 ≤ ∑ i ∈ s, y i := Finset.sum_nonneg (fun i _ => hy i)
    have hZ : 0 ≤ ∑ i ∈ s, z i := Finset.sum_nonneg (fun i _ => hz i)
    have hCS : (∑ i ∈ s, z i) ^ 2 ≤ (∑ i ∈ s, x i) * ∑ i ∈ s, y i :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => hx i) (fun i _ => hy i)
        (fun i _ => hxyz i)
    have hG := G_psd hp (hx j) hX (hy j) hY (hz j) hZ (hxyz j) hCS
    have e : ∀ a S T : ℝ, (a + S) ^ p - (a ^ p + T) = G p a S + (S ^ p - T) := by
      intro a S T; unfold G; ring
    rw [e, e, e]
    exact hG.add ih

/-- The final scalar step: the positive semidefinite defect matrix and the scalar
Cauchy-Schwarz inequality `√(ab) + √((1-a)(1-b)) ≤ 1` (in homogeneous form). -/
lemma final_step {P Q a b d Zp : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : PSD2 (P - a) (Q - b) (Zp - d)) : √a * √b - d ≤ √P * √Q - Zp := by
  obtain ⟨h1, h2, h3⟩ := h
  have hP : 0 ≤ P := by linarith
  have hQ : 0 ≤ Q := by linarith
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ P = u ^ 2 := ⟨√P, Real.sqrt_nonneg _, (Real.sq_sqrt hP).symm⟩
  obtain ⟨u', hu', rfl⟩ : ∃ u', 0 ≤ u' ∧ Q = u' ^ 2 :=
    ⟨√Q, Real.sqrt_nonneg _, (Real.sq_sqrt hQ).symm⟩
  obtain ⟨e, he, rfl⟩ : ∃ e, 0 ≤ e ∧ a = e ^ 2 := ⟨√a, Real.sqrt_nonneg _, (Real.sq_sqrt ha).symm⟩
  obtain ⟨e', he', rfl⟩ : ∃ e', 0 ≤ e' ∧ b = e' ^ 2 :=
    ⟨√b, Real.sqrt_nonneg _, (Real.sq_sqrt hb).symm⟩
  rw [Real.sqrt_sq hu, Real.sqrt_sq hu', Real.sqrt_sq he, Real.sqrt_sq he']
  have hue : e ≤ u := by nlinarith
  have hue' : e' ≤ u' := by nlinarith
  have hS : 0 ≤ u * u' - e * e' := by nlinarith [mul_le_mul hue hue' he' hu]
  have hsq : (Zp - d) ^ 2 ≤ (u * u' - e * e') ^ 2 := by
    nlinarith [sq_nonneg (u * e' - e * u')]
  by_contra hlt
  push Not at hlt
  have : u * u' - e * e' < Zp - d := by linarith
  have hT := mul_self_lt_mul_self hS this
  nlinarith

lemma sqrt_rpow_eq {X p : ℝ} (hX : 0 ≤ X) : (√X) ^ p = √(X ^ p) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hX, ← Real.rpow_mul hX, mul_comm]

/-- **Theorem 1, sum form.** For real `p ≥ 2` and nonnegative real vectors `v, w` of any
length `n`,
`‖v^p‖ ‖w^p‖ - ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p - ⟨v, w⟩^p`,
with every norm and inner product written out as a finite sum. -/
theorem main_sum (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (v w : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    √(∑ i, (v i ^ p) ^ 2) * √(∑ i, (w i ^ p) ^ 2) - ∑ i, v i ^ p * w i ^ p
      ≤ (√(∑ i, v i ^ 2)) ^ p * (√(∑ i, w i ^ 2)) ^ p - (∑ i, v i * w i) ^ p := by
  have hS := sum_psd hp Finset.univ (fun i => v i ^ 2) (fun i => w i ^ 2) (fun i => v i * w i)
    (fun i => sq_nonneg _) (fun i => sq_nonneg _) (fun i => mul_nonneg (hv i) (hw i))
    (fun i => by rw [mul_pow])
  have e1 : ∀ i, (v i ^ p) ^ 2 = (v i ^ 2) ^ p := fun i => by
    rw [sq, sq, Real.mul_rpow (hv i) (hv i)]
  have e2 : ∀ i, (w i ^ p) ^ 2 = (w i ^ 2) ^ p := fun i => by
    rw [sq, sq, Real.mul_rpow (hw i) (hw i)]
  have e3 : ∀ i, v i ^ p * w i ^ p = (v i * w i) ^ p := fun i => (Real.mul_rpow (hv i) (hw i)).symm
  simp only [e1, e2, e3]
  rw [sqrt_rpow_eq (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))),
    sqrt_rpow_eq (Finset.sum_nonneg (fun i _ => sq_nonneg (w i)))]
  exact final_step (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (sq_nonneg _) _))
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (sq_nonneg _) _)) hS

/-- Entrywise real power of a vector in `ℝⁿ` with the Euclidean structure. -/
noncomputable def epow {n : ℕ} (p : ℝ) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => v i ^ p)

/-- **Theorem 1 (Principia Math writeup), resolving Conjecture 5.1 of Johnston, Plosker,
Torrance and Varona.** For every `n`, every real `p ≥ 2` and all entrywise nonnegative
`v, w ∈ ℝⁿ` (Euclidean norm and inner product),
`‖v^p‖ ‖w^p‖ - ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p - ⟨v, w⟩^p`. -/
theorem generalized_cauchy_schwarz (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (v w : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w)
      ≤ ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p := by
  have h := main_sum n p hp (fun i => v i) (fun i => w i) hv hw
  simp only [EuclideanSpace.norm_eq, PiLp.inner_apply, epow, Real.norm_eq_abs, sq_abs,
    RCLike.inner_apply, conj_trivial]
  convert h using 3 <;> simp [mul_comm]

/-- Conjecture 5.1 of Johnston, Plosker, Torrance and Varona, as rendered in the Principia
Math writeup: for every `n ≥ 1`, every real `p ≥ 2` and all entrywise strictly positive
`v, w ∈ ℝⁿ`, `‖v^p‖ ‖w^p‖ - ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p - ⟨v, w⟩^p`. -/
def Conjecture_5_1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 2 ≤ p → ∀ v w : EuclideanSpace ℝ (Fin n),
    (∀ i, 0 < v i) → (∀ i, 0 < w i) →
      ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w)
        ≤ ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p

/-- Conjecture 5.1 holds. -/
theorem conjecture_5_1_true : Conjecture_5_1 :=
  fun n _ p hp v w hv hw =>
    generalized_cauchy_schwarz n p hp v w (fun i => (hv i).le) (fun i => (hw i).le)

end RealPowerCauchySchwarz
