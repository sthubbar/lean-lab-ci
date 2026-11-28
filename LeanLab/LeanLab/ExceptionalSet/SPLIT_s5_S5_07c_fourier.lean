/-
Split of the LEAF `leaf_s5_07b_fourier_hasSum` of
`LeanLab.ExceptionalSet.SPLIT_s5_S5_07b_squarewave`, KEEP GOING unit S5-07c, CLOUD S5
burst-20261127. P0082 Bruedern and Perelli 1998, §7, p. 370, display (40).

The averaged square wave `s5AvgWave Δ` is a continuous function of period `2`.  Its Fourier
coefficients at the frequencies `h/2` are `s5SqCoeff Δ h`, and these are absolutely summable,
so by `hasSum_fourier_series_of_summable` of Mathlib its Fourier series converges to it at
every point.  The split:

* `leaf_s5_07c_coeff`, MEDIUM, the only open piece:
  `(1/2) ∫_0^2 e(-h y/2) s5AvgWave Δ y dy = s5SqCoeff Δ h`, the coefficient computation of
  display (40), by Fubini and the coefficient `2/(π i h)` of the wave.

Proved here: `s5_07c_continuous`, an integral of a bounded measurable function between moving
limits; `s5_07c_periodic`, since `(-1)^{⌊t + 2⌋} = (-1)^{⌊t⌋}`; `s5_07c_coeff_le_sq`, `‖s5SqCoeff Δ h‖ ≤ (2/(9Δ)) / h²`, and hence the summability;
and the assembly `leaf_s5_07b_fourier_hasSum_of_leaves`, the exact statement of the leaf being
split, through Mathlib's `hasSum_fourier_series_of_summable` on `AddCircle 2`.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_07b_squarewave

namespace LeanLab.ExceptionalSet.U1539

/-- Display (40), p. 370, continuity of the smoothed square wave, proved. The map
`y ↦ (1/(2Δ)) ∫_{y-Δ}^{y+Δ} (-1)^{⌊t⌋} dt` is continuous: it is a difference of two values of a
primitive of a bounded measurable function. -/
theorem s5_07c_continuous (Δ : ℝ) (hΔ₀ : 0 < Δ) : Continuous (s5AvgWave Δ) := by
  set g : ℝ → ℂ := fun t => (-1 : ℂ) ^ ⌊t⌋ with hgdef
  have hmeas : Measurable g := by
    have h1 : Measurable (fun k : ℤ => (-1 : ℂ) ^ k) := measurable_of_countable _
    exact h1.comp Int.measurable_floor
  have hint : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => ?_))
    simp only [hgdef, norm_zpow, norm_neg, norm_one, one_zpow, le_refl]
  have hG := intervalIntegral.continuous_primitive hint 0
  have heq : s5AvgWave Δ = fun y => ((1 / (2 * Δ) : ℝ) : ℂ) *
      ((∫ t in (0 : ℝ)..(y + Δ), g t) - ∫ t in (0 : ℝ)..(y - Δ), g t) := by
    funext y
    unfold s5AvgWave
    rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  rw [heq]
  exact continuous_const.mul ((hG.comp (continuous_id.add continuous_const)).sub
    (hG.comp (continuous_id.sub continuous_const)))

/-- Display (40), p. 370, the smoothed square wave has period `2`, proved:
`(-1)^{⌊t + 2⌋} = (-1)^{⌊t⌋}`, and the window moves with `y`. -/
theorem s5_07c_periodic (Δ : ℝ) (hΔ₀ : 0 < Δ) : Function.Periodic (s5AvgWave Δ) 2 := by
  intro y
  unfold s5AvgWave
  congr 1
  have hg : ∀ x : ℝ, (-1 : ℂ) ^ ⌊x + 2⌋ = (-1 : ℂ) ^ ⌊x⌋ := by
    intro x
    have : ⌊x + 2⌋ = ⌊x⌋ + 2 := by
      have := Int.floor_add_intCast x 2
      simpa using this
    rw [this, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    norm_num
  rw [show y + 2 - Δ = (y - Δ) + 2 by ring, show y + 2 + Δ = (y + Δ) + 2 by ring,
    ← intervalIntegral.integral_comp_add_right (fun t => (-1 : ℂ) ^ ⌊t⌋) 2]
  simp only [hg]

/-- LEAF: display (40), p. 370, the Fourier coefficients of the smoothed square wave, MEDIUM.
`(1/2) ∫_0^2 e(-h y/2) s5AvgWave Δ y dy = s5SqCoeff Δ h`: by Fubini the coefficient of the
average is the coefficient `2/(π i h)` of the wave, `h` odd, `0` for `h` even, times the
average `sin(π h Δ)/(π h Δ)` of `e(h u/2)` over `|u| ≤ Δ`. -/
theorem leaf_s5_07c_coeff (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (h : ℤ) :
    (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * s5AvgWave Δ y = s5SqCoeff Δ h := by
  sorry

/-- `‖s5SqCoeff Δ h‖ ≤ (2/(9Δ)) / h²`; for `h = 0` both sides vanish. -/
theorem s5_07c_coeff_le_sq (Δ : ℝ) (hΔ₀ : 0 < Δ) (h : ℤ) :
    ‖s5SqCoeff Δ h‖ ≤ 2 / (9 * Δ) * (1 / (h : ℝ) ^ 2) := by
  have hpi := Real.pi_gt_three
  unfold s5SqCoeff
  split_ifs with ho
  · have hh0 : (h : ℝ) ≠ 0 := by
      intro hz
      have : h = 0 := by exact_mod_cast hz
      rw [this] at ho
      exact (by simp : ¬ Odd (0 : ℤ)) ho
    rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hx0 : Real.pi * h * Δ ≠ 0 := by positivity
    have hval : 2 / (Real.pi * h) * (Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ))
        = Real.sin (Real.pi * h * Δ) * (2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2)) := by
      field_simp
    rw [hval, abs_mul]
    have hs1 : |Real.sin (Real.pi * h * Δ)| ≤ 1 := Real.abs_sin_le_one _
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2))]
    have hpi2 : 9 < Real.pi ^ 2 := by nlinarith
    have hle : 2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2) ≤ 2 / (9 * Δ) * (1 / (h : ℝ) ^ 2) := by
      rw [mul_one_div, div_div]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : 0 < Δ * (h : ℝ) ^ 2 := by positivity
      nlinarith
    calc |Real.sin (Real.pi * h * Δ)| * (2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2))
        ≤ 1 * (2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hs1 (by positivity)
      _ ≤ _ := by rw [one_mul]; exact hle
  · rw [norm_zero]; positivity

/-- The coefficients `s5SqCoeff Δ` are absolutely summable. -/
theorem s5_07c_summable (Δ : ℝ) (hΔ₀ : 0 < Δ) : Summable (s5SqCoeff Δ) := by
  apply Summable.of_norm_bounded _ (s5_07c_coeff_le_sq Δ hΔ₀)
  exact (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left _

/-- `leaf_s5_07b_fourier_hasSum`, exact statement, from the coefficient leaf, the proved pieces and Mathlib's
`hasSum_fourier_series_of_summable`. -/
theorem leaf_s5_07b_fourier_hasSum_of_leaves (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (y : ℝ) :
    HasSum (fun h : ℤ => s5SqCoeff Δ h * eC (h / 2 * y)) (s5AvgWave Δ y) := by
  have : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩
  have hp := s5_07c_periodic Δ hΔ₀
  set f : C(AddCircle (2 : ℝ), ℂ) :=
    ⟨hp.lift, continuous_coinduced_dom.mpr (s5_07c_continuous Δ hΔ₀)⟩ with hfdef
  have hfour : ∀ (n : ℤ) (x : ℝ), fourier n (x : AddCircle (2 : ℝ)) = eC (n / 2 * x) := by
    intro n x
    rw [fourier_coe_apply]
    unfold eC
    congr 1
    push_cast
    ring
  have hfc : ∀ n : ℤ, fourierCoeff f n = s5SqCoeff Δ n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral f n 0, zero_add, ← leaf_s5_07c_coeff Δ hΔ₀ hΔ₁ n,
      Complex.real_smul]
    congr 1
    · norm_num
    · apply intervalIntegral.integral_congr
      intro x _
      simp only [hfdef, ContinuousMap.coe_mk, Function.Periodic.lift_coe, smul_eq_mul]
      rw [hfour]
      congr 2
      push_cast
      ring
  have hsum : Summable (fourierCoeff f) := by
    have : fourierCoeff f = s5SqCoeff Δ := funext hfc
    rw [this]; exact s5_07c_summable Δ hΔ₀
  have H := (hasSum_fourier_series_of_summable hsum).mapL
    (ContinuousMap.evalCLM ℂ ((y : ℝ) : AddCircle (2 : ℝ)))
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, hfc, smul_eq_mul] at H
  have hval : f ((y : ℝ) : AddCircle (2 : ℝ)) = s5AvgWave Δ y := by
    simp only [hfdef, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
  rw [hval] at H
  convert H using 2 with n
  rw [hfour]

/-- Twin check: the assembly has the type of the leaf being split. -/
example : type_of% @leaf_s5_07b_fourier_hasSum := @leaf_s5_07b_fourier_hasSum_of_leaves

end LeanLab.ExceptionalSet.U1539
