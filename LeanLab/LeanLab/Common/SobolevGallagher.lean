/-
The Sobolev-Gallagher inequality, Montgomery, Topics in Multiplicative Number Theory, LNM 227,
Lemma 1.1, in the form used by Languasco-Perelli 1996, P0071, proof of Lemma 2, page 355, and by
Gallagher's large sieve: for `f` with derivative `f'` on `[a, b]` and `x₀ ∈ [a, b]`,
`|f(x₀)| ≤ (b - a)⁻¹ ∫_a^b |f| + ∫_a^b |f'|`.
Unit U-5078, CLOUD 20261019T0213Z-cloud14. KNOWN mathematics, shared infrastructure.
Also `sobolev_gallagher_sq`, the squared form for curves in a real inner product space.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Common
open intervalIntegral MeasureTheory

/-- `|∫_t^s g| ≤ ∫_a^b g` for `g ≥ 0` on `[a, b]` and `t, s ∈ [a, b]`. -/
theorem abs_integral_sub_le {g : ℝ → ℝ} {a b t s : ℝ} (ht : t ∈ Set.Icc a b) (hs : s ∈ Set.Icc a b)
    (hg0 : ∀ u ∈ Set.Icc a b, 0 ≤ g u) (hg : IntervalIntegrable g volume a b) :
    |∫ u in t..s, g u| ≤ ∫ u in a..b, g u := by
  have hab : a ≤ b := le_trans ht.1 ht.2
  have hsub : ∀ c d, c ∈ Set.Icc a b → d ∈ Set.Icc a b → c ≤ d →
      0 ≤ ∫ u in c..d, g u ∧ ∫ u in c..d, g u ≤ ∫ u in a..b, g u := by
    intro c d hc hd hcd
    refine ⟨integral_nonneg hcd fun u hu => hg0 u ⟨le_trans hc.1 hu.1, le_trans hu.2 hd.2⟩, ?_⟩
    apply integral_mono_interval hc.1 hcd hd.2
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact hg0 u ⟨le_of_lt hu.1, hu.2⟩
    · exact hg
  rcases le_total t s with h | h
  · obtain ⟨h0, h1⟩ := hsub t s ht hs h
    rw [abs_of_nonneg h0]; exact h1
  · obtain ⟨h0, h1⟩ := hsub s t hs ht h
    rw [integral_symm, abs_neg, abs_of_nonneg h0]; exact h1

/-- **Sobolev-Gallagher.** -/
theorem sobolev_gallagher {f f' : ℝ → ℝ} {a b x₀ : ℝ} (hab : a < b) (hx : x₀ ∈ Set.Icc a b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t) (hf' : IntervalIntegrable f' volume a b) :
    |f x₀| ≤ (∫ t in a..b, |f t|) / (b - a) + ∫ t in a..b, |f' t| := by
  have hab' : a ≤ b := hab.le
  have hcont : ContinuousOn f (Set.Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable (fun t => |f t|) volume a b :=
    (hcont.abs).intervalIntegrable_of_Icc hab'
  have hf'i : IntervalIntegrable (fun t => |f' t|) volume a b := hf'.abs
  set I' := ∫ t in a..b, |f' t| with hI'
  -- pointwise
  have hpt : ∀ t ∈ Set.Icc a b, |f x₀| ≤ |f t| + I' := by
    intro t ht
    have hsub : Set.uIcc t x₀ ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab']; exact Set.uIcc_subset_Icc ht hx
    have hftc : ∫ s in t..x₀, f' s = f x₀ - f t :=
      integral_eq_sub_of_hasDerivAt (fun s hs => hf s (by
        have := hsub hs; rwa [Set.uIcc_of_le hab'] at this))
        (hf'.mono_set hsub)
    have h1 : |∫ s in t..x₀, f' s| ≤ abs (∫ s in t..x₀, |f' s|) := by
      have := norm_integral_le_abs_integral_norm (a := t) (b := x₀) (f := f') (μ := volume)
      simpa [Real.norm_eq_abs] using this
    have h2 := abs_integral_sub_le ht hx (fun u _ => abs_nonneg (f' u)) hf'i
    have : |f x₀| ≤ |f t| + |f x₀ - f t| := by
      have := abs_add_le (f t) (f x₀ - f t); simp only [add_sub_cancel] at this; linarith
    rw [← hftc] at this
    linarith
  -- integrate over t
  have hint : ∫ t in a..b, |f x₀| ≤ ∫ t in a..b, (|f t| + I') :=
    integral_mono_on hab' intervalIntegrable_const (hfi.add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const, integral_add hfi intervalIntegrable_const,
    intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul] at hint
  have hba : 0 < b - a := by linarith
  rw [div_add' _ _ _ hba.ne', le_div_iff₀ hba]
  linarith

/-- The form of P0071 (12): `|G(0)| ≤ ∫_{-1}^{1} |G| + ∫_{-1}^{1} |G'|`. -/
theorem sobolev_gallagher_unit {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : IntervalIntegrable f' volume (-1) 1) :
    |f 0| ≤ (∫ t in (-1 : ℝ)..1, |f t|) + ∫ t in (-1 : ℝ)..1, |f' t| := by
  have h := sobolev_gallagher (a := -1) (b := 1) (x₀ := 0) (by norm_num) ⟨by norm_num, by norm_num⟩
    hf hf'
  have h0 : 0 ≤ ∫ t in (-1 : ℝ)..1, |f t| :=
    integral_nonneg (by norm_num) fun t _ => abs_nonneg _
  norm_num at h
  linarith

/-- The squared form, for a curve `s` in a real inner product space, `ℂ` included: for every
`c > 0`, `‖s(0)‖² ≤ (1 + c) ∫_{-1}^{1} ‖s‖² + c⁻¹ ∫_{-1}^{1} ‖s'‖²`. With `G = ‖s‖²`,
`|G'| = 2|⟪s, s'⟫| ≤ c‖s‖² + c⁻¹‖s'‖²`; this replaces the Cauchy-Schwarz step of P0071 (12). -/
theorem sobolev_gallagher_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {s s' : ℝ → F} (hs : ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt s (s' t) t)
    (hs' : ContinuousOn s' (Set.Icc (-1 : ℝ) 1)) {c : ℝ} (hc : 0 < c) :
    ‖s 0‖ ^ 2 ≤ (1 + c) * (∫ t in (-1 : ℝ)..1, ‖s t‖ ^ 2) + c⁻¹ * ∫ t in (-1 : ℝ)..1, ‖s' t‖ ^ 2 := by
  have hcont : ContinuousOn s (Set.Icc (-1 : ℝ) 1) :=
    fun t ht => (hs t ht).continuousAt.continuousWithinAt
  have hG : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivAt (fun t => ‖s t‖ ^ 2) (2 * inner ℝ (s t) (s' t)) t :=
    fun t ht => (hs t ht).norm_sq
  have hG'c : ContinuousOn (fun t => 2 * inner ℝ (s t) (s' t)) (Set.Icc (-1 : ℝ) 1) :=
    continuousOn_const.mul (hcont.inner hs')
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have h := sobolev_gallagher_unit hG (hG'c.intervalIntegrable_of_Icc hle)
  have hA : IntervalIntegrable (fun t => ‖s t‖ ^ 2) volume (-1) 1 :=
    ((hcont.norm).pow 2).intervalIntegrable_of_Icc hle
  have hB : IntervalIntegrable (fun t => ‖s' t‖ ^ 2) volume (-1) 1 :=
    ((hs'.norm).pow 2).intervalIntegrable_of_Icc hle
  have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      |2 * inner ℝ (s t) (s' t)| ≤ c * ‖s t‖ ^ 2 + c⁻¹ * ‖s' t‖ ^ 2 := by
    intro t _
    have h1 := abs_real_inner_le_norm (s t) (s' t)
    rw [abs_mul, abs_two]
    have hci : 0 < c⁻¹ := inv_pos.mpr hc
    have key : 2 * (‖s t‖ * ‖s' t‖) ≤ c * ‖s t‖ ^ 2 + c⁻¹ * ‖s' t‖ ^ 2 := by
      have hsq := sq_nonneg (c * ‖s t‖ - ‖s' t‖)
      have e : c⁻¹ * (c * ‖s t‖ - ‖s' t‖) ^ 2 =
          c * ‖s t‖ ^ 2 + c⁻¹ * ‖s' t‖ ^ 2 - 2 * (‖s t‖ * ‖s' t‖) := by
        field_simp; ring
      nlinarith [mul_nonneg hci.le hsq]
    linarith
  have hint : ∫ t in (-1 : ℝ)..1, |2 * inner ℝ (s t) (s' t)| ≤
      ∫ t in (-1 : ℝ)..1, (c * ‖s t‖ ^ 2 + c⁻¹ * ‖s' t‖ ^ 2) :=
    integral_mono_on hle (hG'c.intervalIntegrable_of_Icc hle).abs
      ((hA.const_mul c).add (hB.const_mul _)) hpt
  rw [integral_add (hA.const_mul c) (hB.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  have habs : ∀ t, |‖s t‖ ^ 2| = ‖s t‖ ^ 2 := fun t => abs_of_nonneg (sq_nonneg _)
  simp only [habs] at h
  linarith

end LeanLab.Common
