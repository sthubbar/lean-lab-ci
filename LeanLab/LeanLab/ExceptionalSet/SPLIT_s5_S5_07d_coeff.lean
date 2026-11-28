/-
Split of the LEAF `leaf_s5_07c_coeff` of `LeanLab.ExceptionalSet.SPLIT_s5_S5_07c_fourier`,
KEEP GOING unit S5-07d, CLOUD S5 burst-20261127. P0082 Bruedern and Perelli 1998, §7, p. 370,
display (40).

The Fourier coefficient of the averaged square wave at frequency `h/2` is the coefficient of the
square wave times the average `sin(π h Δ)/(π h Δ)` of `e(h u/2)` over `|u| ≤ Δ`.  The split:

* `leaf_s5_07d_average_multiplier`, MEDIUM, the only open piece: that multiplier identity, by
  Fubini on `[0, 2] × [-Δ, Δ]` and the period `2` of the wave.  For `h = 0` both sides vanish,
  the wave having mean zero, which matches Lean's `0/0 = 0`.

Proved here: `s5_07d_wave_coeff`, the coefficient of `(-1)^{⌊y⌋}` itself,
`(1/2) ∫_0^2 e(-h y/2) (-1)^{⌊y⌋} dy = 2/(π i h)` for odd `h` and `0` for even `h`; and the
assembly `leaf_s5_07c_coeff_of_leaves`, the exact statement of the leaf being split.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_07c_fourier

namespace LeanLab.ExceptionalSet.U1539

/-- LEAF: display (40), p. 370, averaging multiplies the Fourier coefficients, MEDIUM. Writing
`s5AvgWave Δ y = (1/(2Δ)) ∫_{-Δ}^{Δ} (-1)^{⌊y + u⌋} du`, Fubini on `[0, 2] × [-Δ, Δ]` and the
period `2` of `(-1)^{⌊y⌋}` give that the coefficient of the average at frequency `h/2` is
`(1/(2Δ)) ∫_{-Δ}^{Δ} e(h u/2) du = sin(π h Δ)/(π h Δ)` times the coefficient of the wave. -/
theorem leaf_s5_07d_average_multiplier (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (h : ℤ) :
    (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * s5AvgWave Δ y
      = ((Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ) : ℝ) : ℂ) *
        ((1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋) := by
  sorry

/-- The Fourier coefficient of the square wave `(-1)^{⌊y⌋}` of period `2` at frequency `h/2`:
`2/(π i h) = (2/(π h)) (-i)` for odd `h`, `0` for even `h`. -/
theorem s5_07d_wave_coeff (h : ℤ) :
    (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋
      = if Odd h then ((2 / (Real.pi * h) : ℝ) : ℂ) * (-Complex.I) else 0 := by
  set c : ℂ := -(Real.pi * h) * Complex.I with hc
  have hE : ∀ y : ℝ, eC (-(h / 2 * y)) = Complex.exp (c * y) := by
    intro y; unfold eC; rw [hc]; congr 1; push_cast; ring
  set g : ℝ → ℂ := fun t => (-1 : ℂ) ^ ⌊t⌋ with hgdef
  have hmeas : Measurable g := by
    have h1 : Measurable (fun k : ℤ => (-1 : ℂ) ^ k) := measurable_of_countable _
    exact h1.comp Int.measurable_floor
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun y => eC (-(h / 2 * y)) * g y)
      MeasureTheory.volume a b := by
    intro a b
    have hg : IntervalIntegrable g MeasureTheory.volume a b := by
      refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun t => ?_))
      simp only [hgdef, norm_zpow, norm_neg, norm_one, one_zpow, le_refl]
    apply hg.continuousOn_mul
    simp only [hE]
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hint 0 1) (hint 1 2)]
  have h01 : ∫ y in (0 : ℝ)..1, eC (-(h / 2 * y)) * g y = ∫ y in (0 : ℝ)..1, Complex.exp (c * y) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem MeasureTheory.volume] with t hne ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have hlt : t < 1 := lt_of_le_of_ne ht.2 (by simpa using hne)
    have hfl : ⌊t⌋ = 0 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [ht.1]
    simp only [hgdef, hfl, zpow_zero, mul_one, hE]
  have h12 : ∫ y in (1 : ℝ)..2, eC (-(h / 2 * y)) * g y = -∫ y in (1 : ℝ)..2, Complex.exp (c * y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Set.countable_singleton (2 : ℝ)).ae_notMem MeasureTheory.volume] with t hne ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have hlt : t < 2 := lt_of_le_of_ne ht.2 (by simpa using hne)
    have hfl : ⌊t⌋ = 1 := by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [ht.1]
    simp only [hgdef, hfl, zpow_one, mul_neg_one, hE]
  rw [h01, h12]
  have hexp1 : Complex.exp c = (-1 : ℂ) ^ h := by
    rw [hc, show (-(Real.pi * h) * Complex.I : ℂ) = (-h : ℤ) * (Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I, zpow_neg]
    rcases Int.even_or_odd h with he | ho
    · rw [he.neg_one_zpow, inv_one]
    · rw [ho.neg_one_zpow]; norm_num
  by_cases h0 : h = 0
  · subst h0
    have hcz : c = 0 := by rw [hc]; simp
    simp only [hcz, zero_mul, Complex.exp_zero, intervalIntegral.integral_const]
    rw [if_neg (by simp : ¬ Odd (0 : ℤ))]
    norm_num
  have hc0 : c ≠ 0 := by
    rw [hc]
    have : (h : ℂ) ≠ 0 := by exact_mod_cast h0
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, hpi, Complex.I_ne_zero]
  rw [integral_exp_mul_complex hc0, integral_exp_mul_complex hc0]
  have hexp2 : Complex.exp (c * ((2 : ℝ) : ℂ)) = 1 := by
    rw [show c * ((2 : ℝ) : ℂ) = c + c by push_cast; ring, Complex.exp_add, hexp1, ← zpow_add₀ (by norm_num)]
    rw [show h + h = 2 * h by ring, zpow_mul]; norm_num
  have hexpc : Complex.exp (c * ((1 : ℝ) : ℂ)) = (-1 : ℂ) ^ h := by
    rw [Complex.ofReal_one, mul_one, hexp1]
  have hexp0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [hexp2, hexpc, hexp0]
  have hh : (h : ℂ) ≠ 0 := by exact_mod_cast h0
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  split_ifs with ho
  · rw [ho.neg_one_zpow, hc]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]; ring
  · rw [(Int.not_odd_iff_even.mp ho).neg_one_zpow]
    ring

/-- `leaf_s5_07c_coeff`, exact statement, from the multiplier leaf and `s5_07d_wave_coeff`. -/
theorem leaf_s5_07c_coeff_of_leaves (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (h : ℤ) :
    (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * s5AvgWave Δ y = s5SqCoeff Δ h := by
  rw [leaf_s5_07d_average_multiplier Δ hΔ₀ hΔ₁ h, s5_07d_wave_coeff h]
  unfold s5SqCoeff
  split_ifs
  · push_cast; ring
  · simp

/-- Twin check: the assembly has the type of the leaf being split. -/
example : type_of% @leaf_s5_07c_coeff := @leaf_s5_07c_coeff_of_leaves

end LeanLab.ExceptionalSet.U1539
