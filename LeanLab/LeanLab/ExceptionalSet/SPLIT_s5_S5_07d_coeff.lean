/-
Split of the LEAF `leaf_s5_07c_coeff` of `LeanLab.ExceptionalSet.SPLIT_s5_S5_07c_fourier`,
KEEP GOING unit S5-07d, CLOUD S5 burst-20261127. P0082 Bruedern and Perelli 1998, §7, p. 370,
display (40).

The Fourier coefficient of the averaged square wave at frequency `h/2` is the coefficient of the
square wave times the average `sin(π h Δ)/(π h Δ)` of `e(h u/2)` over `|u| ≤ Δ`.  The split:

* `leaf_s5_07d_average_multiplier`: that multiplier identity, by Fubini on `[0, 2] × [-Δ, Δ]`
  and the period `2` of the wave.  For `h = 0` both sides vanish, the wave having mean zero,
  which matches Lean's `0/0 = 0`.  It was a MEDIUM LEAF on S5-07d and is PROVED in place by
  unit S5-07e, with `s5_07e_exp_avg`, `s5_07e_eC_int` and `s5_07e_key`.  This file has no sorry.

Proved here: `s5_07d_wave_coeff`, the coefficient of `(-1)^{⌊y⌋}` itself,
`(1/2) ∫_0^2 e(-h y/2) (-1)^{⌊y⌋} dy = 2/(π i h)` for odd `h` and `0` for even `h`; and the
assembly `leaf_s5_07c_coeff_of_leaves`, the exact statement of the leaf being split.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_07c_fourier

namespace LeanLab.ExceptionalSet.U1539

open MeasureTheory in
private theorem s5e_eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem s5_07e_g_meas : Measurable (fun t : ℝ => (-1 : ℂ) ^ ⌊t⌋) :=
  (measurable_of_countable (fun k : ℤ => (-1 : ℂ) ^ k)).comp Int.measurable_floor

theorem s5_07e_exp_avg (h : ℤ) (hh : h ≠ 0) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∫ u in (-Δ)..Δ, eC (h / 2 * u)
      = ((2 * Δ : ℝ) : ℂ) * ((Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ) : ℝ) : ℂ) := by
  set c : ℂ := (Real.pi * h) * Complex.I with hc
  have hE : ∀ u : ℝ, eC (h / 2 * u) = Complex.exp (c * u) := by
    intro u; unfold eC; rw [hc]; congr 1; push_cast; ring
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc0 : c ≠ 0 := by rw [hc]; simp [hh', hpi, Complex.I_ne_zero]
  simp only [hE]
  rw [integral_exp_mul_complex hc0]
  have hx : (Real.pi * h * Δ : ℝ) ≠ 0 := by
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  rw [Complex.ofReal_div, Complex.ofReal_sin]
  set x : ℂ := ((Real.pi * h * Δ : ℝ) : ℂ) with hxdef
  have hsin2 : Complex.sin x * (2 * Complex.I) = Complex.exp (x * Complex.I) - Complex.exp (-(x * Complex.I)) := by
    rw [Complex.sin]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  have hsin : Complex.sin x = (Complex.exp (x * Complex.I) - Complex.exp (-(x * Complex.I))) / (2 * Complex.I) := by
    rw [← hsin2]; field_simp [Complex.I_ne_zero]
  have e1 : c * (Δ : ℂ) = x * Complex.I := by rw [hc, hxdef]; push_cast; ring
  have e2 : c * ((-Δ : ℝ) : ℂ) = -(x * Complex.I) := by rw [hc, hxdef]; push_cast; ring
  rw [e1, e2, hsin]
  have hx0 : x ≠ 0 := by rw [hxdef]; exact_mod_cast hx
  have hΔ' : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  have hxc : x = c * Δ / Complex.I := by
    rw [hc, hxdef]; push_cast; field_simp [Complex.I_ne_zero]
  rw [hxc]
  push_cast
  field_simp [Complex.I_ne_zero]

theorem s5_07e_eC_int (n : ℤ) : eC (n : ℝ) = 1 := by
  unfold eC
  rw [show (2 * Real.pi * Complex.I * ((n : ℝ) : ℂ)) = n * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem s5_07e_key (Δ : ℝ) (hΔ₀ : 0 < Δ) (h : ℤ) :
    ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * s5AvgWave Δ y
      = ((1 / (2 * Δ) : ℝ) : ℂ) * ((∫ u in (-Δ)..Δ, eC (h / 2 * u)) *
        ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋) := by
  set g : ℝ → ℂ := fun t => (-1 : ℂ) ^ ⌊t⌋ with hgdef
  set E : ℝ → ℂ := fun y => eC (-(h / 2 * y)) with hEdef
  have hEc : Continuous E := by rw [hEdef]; unfold eC; fun_prop
  have hW : ∀ y, s5AvgWave Δ y = ((1 / (2 * Δ) : ℝ) : ℂ) * ∫ u in (-Δ)..Δ, g (y + u) := by
    intro y
    unfold s5AvgWave
    congr 1
    rw [intervalIntegral.integral_comp_add_left (fun t => g t) y]
    simp only [hgdef, sub_eq_add_neg]
  have h1 : ∫ y in (0 : ℝ)..2, E y * s5AvgWave Δ y
      = ((1 / (2 * Δ) : ℝ) : ℂ) * ∫ y in (0 : ℝ)..2, ∫ u in (-Δ)..Δ, E y * g (y + u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    simp only
    rw [hW y, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    ring
  have hmeasF : Measurable (Function.uncurry fun y u : ℝ => E y * g (y + u)) := by
    apply Measurable.mul
    · exact hEc.measurable.comp measurable_fst
    · exact s5_07e_g_meas.comp (measurable_fst.add measurable_snd)
  have hint : MeasureTheory.IntegrableOn (Function.uncurry fun y u : ℝ => E y * g (y + u))
      (Set.uIoc 0 2 ×ˢ Set.uIoc (-Δ) Δ) := by
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) ?_ hmeasF.aestronglyMeasurable ?_
    · rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
      exact ENNReal.mul_ne_top (by simp [Set.uIoc]) (by simp [Set.uIoc])
    · refine Filter.Eventually.of_forall (fun p => ?_)
      simp only [Function.uncurry, hEdef, hgdef, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow,
        mul_one]
      unfold eC
      rw [show (2 * Real.pi * Complex.I * ((-(h / 2 * p.1) : ℝ) : ℂ)) =
        ((2 * Real.pi * (-(h / 2 * p.1)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap hint
  have hP : Function.Periodic (fun y => E y * g y) 2 := by
    intro y
    simp only [hEdef, hgdef]
    have hfl : ⌊y + 2⌋ = ⌊y⌋ + 2 := by simpa using Int.floor_add_intCast y 2
    rw [hfl, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      show (-(h / 2 * (y + 2)) : ℝ) = -(h / 2 * y) + ((-h : ℤ) : ℝ) by push_cast; ring,
      s5e_eC_add, s5_07e_eC_int]
    norm_num
  have hinner : ∀ u : ℝ, ∫ y in (0 : ℝ)..2, E y * g (y + u)
      = eC (h / 2 * u) * ∫ y in (0 : ℝ)..2, E y * g y := by
    intro u
    have hEs : ∀ y, E y = eC (h / 2 * u) * E (y + u) := by
      intro y; simp only [hEdef]; rw [← s5e_eC_add]; congr 1; ring
    rw [← intervalIntegral.integral_const_mul]
    have : ∫ y in (0 : ℝ)..2, E y * g (y + u) = ∫ y in (0 : ℝ)..2, eC (h / 2 * u) * (E (y + u) * g (y + u)) := by
      apply intervalIntegral.integral_congr; intro y _; simp only; rw [hEs y]; ring
    rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun y => E y * g y) u, zero_add]
    congr 1
    have := hP.intervalIntegral_add_eq u 0
    rw [zero_add, add_comm] at this
    exact this
  show ∫ y in (0 : ℝ)..2, E y * s5AvgWave Δ y = _
  rw [h1, hswap]
  congr 1
  simp only [hinner]
  rw [intervalIntegral.integral_mul_const]

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

/-- Display (40), p. 370, averaging multiplies the Fourier coefficients, PROVED by unit S5-07e. Writing
`s5AvgWave Δ y = (1/(2Δ)) ∫_{-Δ}^{Δ} (-1)^{⌊y + u⌋} du`, Fubini on `[0, 2] × [-Δ, Δ]` and the
period `2` of `(-1)^{⌊y⌋}` give that the coefficient of the average at frequency `h/2` is
`(1/(2Δ)) ∫_{-Δ}^{Δ} e(h u/2) du = sin(π h Δ)/(π h Δ)` times the coefficient of the wave. -/
theorem leaf_s5_07d_average_multiplier (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (h : ℤ) :
    (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * s5AvgWave Δ y
      = ((Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ) : ℝ) : ℂ) *
        ((1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋) := by
  rw [s5_07e_key Δ hΔ₀ h]
  by_cases h0 : h = 0
  · have hw := s5_07d_wave_coeff h
    rw [h0, if_neg (by simp : ¬ Odd (0 : ℤ))] at hw
    subst h0
    have hC : ∫ y in (0 : ℝ)..2, eC (-(((0 : ℤ) : ℝ) / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋ = 0 := by
      have := hw; simpa using this
    rw [hC]; simp
  · rw [s5_07e_exp_avg h h0 Δ hΔ₀]
    have hΔ' : ((2 * Δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Δ : ℝ) ≠ 0)
    have : ((1 / (2 * Δ) : ℝ) : ℂ) * ((2 * Δ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
    linear_combination (((Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ) : ℝ) : ℂ) *
      ((1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋)) * this


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
