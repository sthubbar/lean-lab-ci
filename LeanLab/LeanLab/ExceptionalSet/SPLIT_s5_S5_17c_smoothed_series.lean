/-
Split of `U1539.leaf_smoothed_square_wave_series` of `SPLIT_leaf_square_wave_trig_approx`,
burst-20261127 unit S5-17c, KEEP GOING after S5-17,
P0082 Bruedern and Perelli 1998, section 7, page 370, display (40).

The leaf is split into the construction of the smoothed square wave with its coefficient
bound, the remaining LEAF `leaf_smoothed_square_wave_circle` of class MEDIUM, and the
convergence of its Fourier series, which is proved here from Mathlib's
`has_pointwise_sum_fourier_series_of_summable` and the summability of the weight `sqW`, itself
a consequence of the proved `leaf_square_wave_weight_sums`.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_square_wave_trig_approx

namespace LeanLab.ExceptionalSet.U1539

/-- The circle `ℝ / 2ℤ` of period two carries the Fourier theory used below. -/
local instance fact_two_pos_s5 : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩

/-! Helpers for `leaf_smoothed_square_wave_circle`, burst-20261127 unit S5-17e, copied with new
names from the proved chain `SPLIT_s5_S5_07b_squarewave`, `SPLIT_s5_S5_07c_fourier` and
`SPLIT_s5_S5_07d_coeff` of branch `claude/ExceptionalSet-S5-07e-p5`, P0082 page 370 display
(40). The smoothed wave is the moving average of `(-1) ^ ⌊t⌋` over `[y - Δ, y + Δ]`.
AI wrote the Lean code. -/

section W2Helpers

open Filter Topology

/-- P0082 p. 370 display (40): the Fourier coefficient at frequency `h/2` of the square wave
`(-1)^{⌊y⌋}` averaged over a window of half width `Δ`, namely `2/(π i h)` times
`sin(π h Δ)/(π h Δ)` for odd `h`, and `0` for even `h`. -/
noncomputable def w2SqCoeff (Δ : ℝ) (h : ℤ) : ℂ :=
  if Odd h then
    ((2 / (Real.pi * h) * (Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ)) : ℝ) : ℂ) *
      (-Complex.I)
  else 0

/-- P0082 p. 370 display (40): the smoothed square wave, the average of `(-1)^{⌊t⌋}` over
`y - Δ ≤ t ≤ y + Δ`. -/
noncomputable def w2AvgWave (Δ y : ℝ) : ℂ :=
  ((1 / (2 * Δ) : ℝ) : ℂ) * ∫ t in (y - Δ)..(y + Δ), (-1 : ℂ) ^ ⌊t⌋

/-- Display (40), p. 370, the smoothing is exact away from the jumps. When `y` is at
distance at least `Δ` from the integers, `(-1)^{⌊t⌋}` is constant on `[y - Δ, y + Δ]` up to the
endpoint `⌊y⌋ + 1`, so the average is `(-1)^{⌊y⌋}`. -/
theorem w2_07b_avg_eq_wave (Δ y : ℝ) (hΔ : 0 < Δ) (h1 : Δ ≤ Int.fract y)
    (h2 : Int.fract y ≤ 1 - Δ) : w2AvgWave Δ y = (-1 : ℂ) ^ ⌊y⌋ := by
  have hfy := Int.floor_add_fract y
  have hae : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (y - Δ) (y + Δ) →
      (-1 : ℂ) ^ ⌊t⌋ = (fun _ : ℝ => (-1 : ℂ) ^ ⌊y⌋) t := by
    filter_upwards [(Set.countable_singleton (y + Δ)).ae_notMem MeasureTheory.volume] with t hne ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hlt : t < y + Δ := lt_of_le_of_ne ht.2 (by simpa using hne)
    have hfl : ⌊t⌋ = ⌊y⌋ := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [ht.1]
    simp only [hfl]
  unfold w2AvgWave
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const]
  have h2Δ : (2 * Δ : ℝ) ≠ 0 := by positivity
  rw [show y + Δ - (y - Δ) = 2 * Δ by ring, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    one_div, inv_mul_cancel₀ h2Δ, Complex.ofReal_one, one_mul]

/-- The coefficient bound of display (40): `‖w2SqCoeff Δ h‖ ≤ 2/(|h|+1)`. -/
theorem w2_07b_coeff_le (Δ : ℝ) (hΔ : 0 < Δ) (h : ℤ) :
    ‖w2SqCoeff Δ h‖ ≤ 2 / (|(h : ℝ)| + 1) := by
  unfold w2SqCoeff
  split_ifs with ho
  · rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hh0 : (h : ℝ) ≠ 0 := by
      intro hz
      have : h = 0 := by exact_mod_cast hz
      rw [this] at ho
      exact (by simp : ¬ Odd (0 : ℤ)) ho
    have hpi := Real.pi_gt_three
    have habs1 : 1 ≤ |(h : ℝ)| := by
      have : (1 : ℤ) ≤ |h| := Int.one_le_abs (by exact_mod_cast hh0)
      have h' : ((|h| : ℤ) : ℝ) = |(h : ℝ)| := by push_cast; rfl
      rw [← h']; exact_mod_cast this
    set x := Real.pi * h * Δ with hx
    have hx0 : x ≠ 0 := by rw [hx]; positivity
    have hsinc : |Real.sin x / x| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr hx0)]
      exact Real.abs_sin_le_abs
    rw [abs_mul]
    have hfirst : |2 / (Real.pi * h)| = 2 / (Real.pi * |(h : ℝ)|) := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    rw [hfirst]
    have hpos : 0 < Real.pi * |(h : ℝ)| := by positivity
    calc 2 / (Real.pi * |(h : ℝ)|) * |Real.sin x / x| ≤ 2 / (Real.pi * |(h : ℝ)|) * 1 :=
          mul_le_mul_of_nonneg_left hsinc (by positivity)
      _ = 2 / (Real.pi * |(h : ℝ)|) := mul_one _
      _ ≤ 2 / (|(h : ℝ)| + 1) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith
  · simp only [norm_zero]; positivity


/-- Display (40), p. 370, continuity of the smoothed square wave, proved. The map
`y ↦ (1/(2Δ)) ∫_{y-Δ}^{y+Δ} (-1)^{⌊t⌋} dt` is continuous: it is a difference of two values of a
primitive of a bounded measurable function. -/
theorem w2_07c_continuous (Δ : ℝ) (hΔ₀ : 0 < Δ) : Continuous (w2AvgWave Δ) := by
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
  have heq : w2AvgWave Δ = fun y => ((1 / (2 * Δ) : ℝ) : ℂ) *
      ((∫ t in (0 : ℝ)..(y + Δ), g t) - ∫ t in (0 : ℝ)..(y - Δ), g t) := by
    funext y
    unfold w2AvgWave
    rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  rw [heq]
  exact continuous_const.mul ((hG.comp (continuous_id.add continuous_const)).sub
    (hG.comp (continuous_id.sub continuous_const)))

/-- Display (40), p. 370, the smoothed square wave has period `2`, proved:
`(-1)^{⌊t + 2⌋} = (-1)^{⌊t⌋}`, and the window moves with `y`. -/
theorem w2_07c_periodic (Δ : ℝ) (hΔ₀ : 0 < Δ) : Function.Periodic (w2AvgWave Δ) 2 := by
  intro y
  unfold w2AvgWave
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

/-- `‖w2SqCoeff Δ h‖ ≤ (2/(9Δ)) / h²`; for `h = 0` both sides vanish. -/
theorem w2_07c_coeff_le_sq (Δ : ℝ) (hΔ₀ : 0 < Δ) (h : ℤ) :
    ‖w2SqCoeff Δ h‖ ≤ 2 / (9 * Δ) * (1 / (h : ℝ) ^ 2) := by
  have hpi := Real.pi_gt_three
  unfold w2SqCoeff
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


open MeasureTheory in
private theorem w2e_eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem w2_07e_g_meas : Measurable (fun t : ℝ => (-1 : ℂ) ^ ⌊t⌋) :=
  (measurable_of_countable (fun k : ℤ => (-1 : ℂ) ^ k)).comp Int.measurable_floor

theorem w2_07e_exp_avg (h : ℤ) (hh : h ≠ 0) (Δ : ℝ) (hΔ : 0 < Δ) :
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

theorem w2_07e_eC_int (n : ℤ) : eC (n : ℝ) = 1 := by
  unfold eC
  rw [show (2 * Real.pi * Complex.I * ((n : ℝ) : ℂ)) = n * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem w2_07e_key (Δ : ℝ) (hΔ₀ : 0 < Δ) (h : ℤ) :
    ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * w2AvgWave Δ y
      = ((1 / (2 * Δ) : ℝ) : ℂ) * ((∫ u in (-Δ)..Δ, eC (h / 2 * u)) *
        ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋) := by
  set g : ℝ → ℂ := fun t => (-1 : ℂ) ^ ⌊t⌋ with hgdef
  set E : ℝ → ℂ := fun y => eC (-(h / 2 * y)) with hEdef
  have hEc : Continuous E := by rw [hEdef]; unfold eC; fun_prop
  have hW : ∀ y, w2AvgWave Δ y = ((1 / (2 * Δ) : ℝ) : ℂ) * ∫ u in (-Δ)..Δ, g (y + u) := by
    intro y
    unfold w2AvgWave
    congr 1
    rw [intervalIntegral.integral_comp_add_left (fun t => g t) y]
    simp only [hgdef, sub_eq_add_neg]
  have h1 : ∫ y in (0 : ℝ)..2, E y * w2AvgWave Δ y
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
    · exact w2_07e_g_meas.comp (measurable_fst.add measurable_snd)
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
      w2e_eC_add, w2_07e_eC_int]
    norm_num
  have hinner : ∀ u : ℝ, ∫ y in (0 : ℝ)..2, E y * g (y + u)
      = eC (h / 2 * u) * ∫ y in (0 : ℝ)..2, E y * g y := by
    intro u
    have hEs : ∀ y, E y = eC (h / 2 * u) * E (y + u) := by
      intro y; simp only [hEdef]; rw [← w2e_eC_add]; congr 1; ring
    rw [← intervalIntegral.integral_const_mul]
    have : ∫ y in (0 : ℝ)..2, E y * g (y + u) = ∫ y in (0 : ℝ)..2, eC (h / 2 * u) * (E (y + u) * g (y + u)) := by
      apply intervalIntegral.integral_congr; intro y _; simp only; rw [hEs y]; ring
    rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun y => E y * g y) u, zero_add]
    congr 1
    have := hP.intervalIntegral_add_eq u 0
    rw [zero_add, add_comm] at this
    exact this
  show ∫ y in (0 : ℝ)..2, E y * w2AvgWave Δ y = _
  rw [h1, hswap]
  congr 1
  simp only [hinner]
  rw [intervalIntegral.integral_mul_const]

/-- The Fourier coefficient of the square wave `(-1)^{⌊y⌋}` of period `2` at frequency `h/2`:
`2/(π i h) = (2/(π h)) (-i)` for odd `h`, `0` for even `h`. -/
theorem w2_07d_wave_coeff (h : ℤ) :
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

/-- Display (40), p. 370, averaging multiplies the Fourier coefficients, proved, copied from unit S5-07e. Writing
`w2AvgWave Δ y = (1/(2Δ)) ∫_{-Δ}^{Δ} (-1)^{⌊y + u⌋} du`, Fubini on `[0, 2] × [-Δ, Δ]` and the
period `2` of `(-1)^{⌊y⌋}` give that the coefficient of the average at frequency `h/2` is
`(1/(2Δ)) ∫_{-Δ}^{Δ} e(h u/2) du = sin(π h Δ)/(π h Δ)` times the coefficient of the wave. -/
theorem w2_07d_average_multiplier (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (h : ℤ) :
    (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * w2AvgWave Δ y
      = ((Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ) : ℝ) : ℂ) *
        ((1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋) := by
  rw [w2_07e_key Δ hΔ₀ h]
  by_cases h0 : h = 0
  · have hw := w2_07d_wave_coeff h
    rw [h0, if_neg (by simp : ¬ Odd (0 : ℤ))] at hw
    subst h0
    have hC : ∫ y in (0 : ℝ)..2, eC (-(((0 : ℤ) : ℝ) / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋ = 0 := by
      have := hw; simpa using this
    rw [hC]; simp
  · rw [w2_07e_exp_avg h h0 Δ hΔ₀]
    have hΔ' : ((2 * Δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Δ : ℝ) ≠ 0)
    have : ((1 / (2 * Δ) : ℝ) : ℂ) * ((2 * Δ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
    linear_combination (((Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ) : ℝ) : ℂ) *
      ((1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋)) * this


/-- The Fourier coefficient of the averaged wave is `w2SqCoeff Δ h`, copied from `leaf_s5_07c_coeff_of_leaves`. -/
theorem w2_07c_coeff (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (h : ℤ) :
    (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * w2AvgWave Δ y = w2SqCoeff Δ h := by
  rw [w2_07d_average_multiplier Δ hΔ₀ hΔ₁ h, w2_07d_wave_coeff h]
  unfold w2SqCoeff
  split_ifs
  · push_cast; ring
  · simp

/-- The coefficient bound of display (40) in the form of `sqW`, proved:
`‖w2SqCoeff Δ h‖ ≤ 2 min(1/|h|, 1/(Δ h²))`, from `w2_07b_coeff_le` and `w2_07c_coeff_le_sq`. -/
theorem w2_coeff_le_sqW (Δ : ℝ) (hΔ : 0 < Δ) (h : ℤ) : ‖w2SqCoeff Δ h‖ ≤ 2 * sqW Δ h := by
  by_cases h0 : h = 0
  · subst h0
    simp [w2SqCoeff, sqW]
  · have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast h0
    have habs : 0 < |(h : ℝ)| := abs_pos.mpr hh0
    have hsq : 0 < (h : ℝ) ^ 2 := by positivity
    unfold sqW
    rw [if_neg h0, mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    refine le_min ((w2_07b_coeff_le Δ hΔ h).trans ?_) ((w2_07c_coeff_le_sq Δ hΔ h).trans ?_)
    · rw [mul_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) habs (by linarith)
    · rw [mul_one_div, mul_one_div, div_div]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [mul_pos hΔ hsq]

end W2Helpers

/-- Proved by unit S5-17e, formerly a LEAF: P0082 page 370 display (40), the smoothed square wave and its coefficients. Class
MEDIUM. For `0 < Δ ≤ 1 / 4` there is a continuous function on the circle `ℝ / 2ℤ`, for example
the square wave `(-1) ^ ⌊x⌋` with its jumps replaced by linear ramps of width `2 Δ` around the
integers, equal to `(-1) ^ ⌊x⌋` when `Δ ≤ {x} ≤ 1 - Δ`, whose Fourier coefficients satisfy
`|c_h| ≤ C min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))`, by integrating by parts once and twice. -/
theorem leaf_smoothed_square_wave_circle :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
      ∃ f : C(AddCircle (2 : ℝ), ℂ), (∀ h : ℤ, ‖fourierCoeff f h‖ ≤ C * sqW Δ h) ∧
        ∀ x : ℝ, Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ →
          f (x : AddCircle (2 : ℝ)) = (-1 : ℂ) ^ ⌊x⌋ := by
  refine ⟨2, by norm_num, fun Δ hΔ hΔ4 => ?_⟩
  have hp := w2_07c_periodic Δ hΔ
  set f : C(AddCircle (2 : ℝ), ℂ) :=
    ⟨hp.lift, continuous_coinduced_dom.mpr (w2_07c_continuous Δ hΔ)⟩ with hfdef
  have hfour : ∀ (n : ℤ) (x : ℝ), fourier n (x : AddCircle (2 : ℝ)) = eC (n / 2 * x) := by
    intro n x
    rw [fourier_coe_apply]
    unfold eC
    congr 1
    push_cast
    ring
  have hfc : ∀ n : ℤ, fourierCoeff f n = w2SqCoeff Δ n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral f n 0, zero_add, ← w2_07c_coeff Δ hΔ hΔ4 n,
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
  refine ⟨f, fun n => (hfc n).symm ▸ w2_coeff_le_sqW Δ hΔ n, fun x h1 h2 => ?_⟩
  simp only [hfdef, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
  exact w2_07b_avg_eq_wave Δ x hΔ h1 h2

/-- Proved: the weight `sqW` is summable over `ℤ`, from `leaf_square_wave_weight_sums` at
`H = 1`. -/
theorem summable_sqW_s5 {Δ : ℝ} (hΔ : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4) : Summable (sqW Δ) := by
  obtain ⟨C, _, hC⟩ := leaf_square_wave_weight_sums
  obtain ⟨h1, h2⟩ := hC Δ hΔ hΔ4 1 le_rfl
  have hnn : ∀ h : ℤ, 0 ≤ sqW Δ h := by
    intro h
    unfold sqW
    split_ifs
    · exact zero_le_one
    · exact le_min (by positivity) (by positivity)
  refine summable_of_sum_le (c := C * (1 + Real.log (1 / Δ)) + C / (Δ * (1 : ℕ)))
    (fun h => hnn h) (fun u => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not u (fun h => h ∈ Finset.Icc (-((1 : ℕ) : ℤ)) (1 : ℕ))]
  refine add_le_add ((Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun h _ _ => hnn h)).trans h1)
    (h2 _ ?_)
  · intro h hh
    exact (Finset.mem_filter.1 hh).2
  · rw [Finset.disjoint_left]
    intro h hh
    exact (Finset.mem_filter.1 hh).2

/-- Proved: `leaf_smoothed_square_wave_series` verbatim, CONDITIONAL ON
`leaf_smoothed_square_wave_circle`; the convergence of the Fourier series is Mathlib's
`has_pointwise_sum_fourier_series_of_summable`. -/
theorem leaf_smoothed_square_wave_series_of_leaves :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
      ∃ c : ℤ → ℂ, (∀ h : ℤ, ‖c h‖ ≤ C * sqW Δ h) ∧
        ∀ x : ℝ, ∃ T : ℂ,
          (Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ → T = (-1 : ℂ) ^ ⌊x⌋) ∧
          HasSum (fun h : ℤ => c h * eC ((h : ℝ) / 2 * x)) T := by
  obtain ⟨C, hC, hf⟩ := leaf_smoothed_square_wave_circle
  refine ⟨C, hC, fun Δ hΔ hΔ4 => ?_⟩
  obtain ⟨f, hcoef, hval⟩ := hf Δ hΔ hΔ4
  have hsum : Summable (fourierCoeff f) :=
    Summable.of_norm_bounded ((summable_sqW_s5 hΔ hΔ4).mul_left C) hcoef
  refine ⟨fourierCoeff f, hcoef, fun x => ⟨f (x : AddCircle (2 : ℝ)),
    fun h1 h2 => hval x h1 h2, ?_⟩⟩
  have hp := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (2 : ℝ))
  refine hp.congr_fun (fun h => ?_)
  rw [smul_eq_mul, fourier_coe_apply]
  unfold eC
  congr 2
  push_cast
  ring

example : type_of% @leaf_smoothed_square_wave_series := leaf_smoothed_square_wave_series_of_leaves

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.leaf_smoothed_square_wave_circle
#print axioms LeanLab.ExceptionalSet.U1539.summable_sqW_s5
#print axioms LeanLab.ExceptionalSet.U1539.leaf_smoothed_square_wave_series_of_leaves
