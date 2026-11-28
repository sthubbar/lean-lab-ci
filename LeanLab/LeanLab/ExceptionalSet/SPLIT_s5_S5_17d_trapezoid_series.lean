/-
Split of `Feed1122ParityCore.leaf_trapezoid_fourier_series` of
`SPLIT_leaf_parity_trapezoid_fourier`, burst-20261127 unit S5-17d, KEEP GOING after S5-17b,
P0082 Bruedern and Perelli 1998, section 7, page 370, display (40).

The leaf is split into the construction of the trapezoid with its coefficient bound, the
LEAF `leaf_trapezoid_circle` of class MEDIUM, PROVED in place by unit S5-17f, and the convergence of its Fourier
series, proved here from Mathlib's `has_pointwise_sum_fourier_series_of_summable` and the
summability of the weight `trapW`, a consequence of the proved `leaf_trapezoid_weight_sums`.


Unit S5-17f proves `leaf_trapezoid_circle` in place: the trapezoid is `(1 + W) / 2` with `W`
the square wave `(-1)^{⌊t⌋}` averaged over half width `A`. The averaged square wave and its
Fourier coefficients, in the namespace `U1539` below, are copied with new names from the sorry
free chain on branches claude/ExceptionalSet-S5-07b-p2 to claude/ExceptionalSet-S5-07e-p5,
files `SPLIT_s5_S5_07b_squarewave`, `SPLIT_s5_S5_07c_fourier` and `SPLIT_s5_S5_07d_coeff`.
This file has no sorry.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_parity_trapezoid_fourier

/-! Copied, with new names, from branches claude/ExceptionalSet-S5-07b-p2 to
claude/ExceptionalSet-S5-07e-p5, files SPLIT_s5_S5_07b_squarewave, SPLIT_s5_S5_07c_fourier and
SPLIT_s5_S5_07d_coeff: P0082 page 370 display (40), the averaged square wave and its
Fourier coefficients. -/

namespace LeanLab.ExceptionalSet.U1539

open Filter Topology

/-- P0082 p. 370 display (40): the Fourier coefficient at frequency `h/2` of the square wave
`(-1)^{⌊y⌋}` averaged over a window of half width `Δ`, namely `2/(π i h)` times
`sin(π h Δ)/(π h Δ)` for odd `h`, and `0` for even `h`. -/
noncomputable def s5fSqCoeff (Δ : ℝ) (h : ℤ) : ℂ :=
  if Odd h then
    ((2 / (Real.pi * h) * (Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ)) : ℝ) : ℂ) *
      (-Complex.I)
  else 0

/-- P0082 p. 370 display (40): the smoothed square wave, the average of `(-1)^{⌊t⌋}` over
`y - Δ ≤ t ≤ y + Δ`. -/
noncomputable def s5fAvgWave (Δ y : ℝ) : ℂ :=
  ((1 / (2 * Δ) : ℝ) : ℂ) * ∫ t in (y - Δ)..(y + Δ), (-1 : ℂ) ^ ⌊t⌋

/-- Display (40), p. 370, the smoothing is exact away from the jumps. When `y` is at
distance at least `Δ` from the integers, `(-1)^{⌊t⌋}` is constant on `[y - Δ, y + Δ]` up to the
endpoint `⌊y⌋ + 1`, so the average is `(-1)^{⌊y⌋}`. -/
theorem s5f_07b_avg_eq_wave (Δ y : ℝ) (hΔ : 0 < Δ) (h1 : Δ ≤ Int.fract y)
    (h2 : Int.fract y ≤ 1 - Δ) : s5fAvgWave Δ y = (-1 : ℂ) ^ ⌊y⌋ := by
  have hfy := Int.floor_add_fract y
  have hae : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (y - Δ) (y + Δ) →
      (-1 : ℂ) ^ ⌊t⌋ = (fun _ : ℝ => (-1 : ℂ) ^ ⌊y⌋) t := by
    filter_upwards [(Set.countable_singleton (y + Δ)).ae_notMem MeasureTheory.volume] with t hne ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hlt : t < y + Δ := lt_of_le_of_ne ht.2 (by simpa using hne)
    have hfl : ⌊t⌋ = ⌊y⌋ := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [ht.1]
    simp only [hfl]
  unfold s5fAvgWave
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const]
  have h2Δ : (2 * Δ : ℝ) ≠ 0 := by positivity
  rw [show y + Δ - (y - Δ) = 2 * Δ by ring, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    one_div, inv_mul_cancel₀ h2Δ, Complex.ofReal_one, one_mul]

/-- The smoothed square wave has modulus at most `1`. -/
theorem s5f_07b_avg_norm_le (Δ y : ℝ) (hΔ : 0 < Δ) : ‖s5fAvgWave Δ y‖ ≤ 1 := by
  unfold s5fAvgWave
  rw [norm_mul]
  have hb : ‖∫ t in (y - Δ)..(y + Δ), (-1 : ℂ) ^ ⌊t⌋‖ ≤ 1 * |(y + Δ) - (y - Δ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    rw [norm_zpow, norm_neg, norm_one, one_zpow]
  have hlen : |(y + Δ) - (y - Δ)| = 2 * Δ := by
    rw [show (y + Δ) - (y - Δ) = 2 * Δ by ring]; exact abs_of_pos (by linarith)
  rw [hlen, one_mul] at hb
  have hc : ‖((1 / (2 * Δ) : ℝ) : ℂ)‖ = 1 / (2 * Δ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  calc 1 / (2 * Δ) * ‖∫ t in (y - Δ)..(y + Δ), (-1 : ℂ) ^ ⌊t⌋‖
      ≤ 1 / (2 * Δ) * (2 * Δ) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 := by field_simp


/-- Display (40), p. 370, continuity of the smoothed square wave, proved. The map
`y ↦ (1/(2Δ)) ∫_{y-Δ}^{y+Δ} (-1)^{⌊t⌋} dt` is continuous: it is a difference of two values of a
primitive of a bounded measurable function. -/
theorem s5f_07c_continuous (Δ : ℝ) (hΔ₀ : 0 < Δ) : Continuous (s5fAvgWave Δ) := by
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
  have heq : s5fAvgWave Δ = fun y => ((1 / (2 * Δ) : ℝ) : ℂ) *
      ((∫ t in (0 : ℝ)..(y + Δ), g t) - ∫ t in (0 : ℝ)..(y - Δ), g t) := by
    funext y
    unfold s5fAvgWave
    rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  rw [heq]
  exact continuous_const.mul ((hG.comp (continuous_id.add continuous_const)).sub
    (hG.comp (continuous_id.sub continuous_const)))

/-- Display (40), p. 370, the smoothed square wave has period `2`, proved:
`(-1)^{⌊t + 2⌋} = (-1)^{⌊t⌋}`, and the window moves with `y`. -/
theorem s5f_07c_periodic (Δ : ℝ) (hΔ₀ : 0 < Δ) : Function.Periodic (s5fAvgWave Δ) 2 := by
  intro y
  unfold s5fAvgWave
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
open MeasureTheory in
private theorem s5f_eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem s5f_07e_g_meas : Measurable (fun t : ℝ => (-1 : ℂ) ^ ⌊t⌋) :=
  (measurable_of_countable (fun k : ℤ => (-1 : ℂ) ^ k)).comp Int.measurable_floor

theorem s5f_07e_exp_avg (h : ℤ) (hh : h ≠ 0) (Δ : ℝ) (hΔ : 0 < Δ) :
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

theorem s5f_07e_eC_int (n : ℤ) : eC (n : ℝ) = 1 := by
  unfold eC
  rw [show (2 * Real.pi * Complex.I * ((n : ℝ) : ℂ)) = n * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem s5f_07e_key (Δ : ℝ) (hΔ₀ : 0 < Δ) (h : ℤ) :
    ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * s5fAvgWave Δ y
      = ((1 / (2 * Δ) : ℝ) : ℂ) * ((∫ u in (-Δ)..Δ, eC (h / 2 * u)) *
        ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋) := by
  set g : ℝ → ℂ := fun t => (-1 : ℂ) ^ ⌊t⌋ with hgdef
  set E : ℝ → ℂ := fun y => eC (-(h / 2 * y)) with hEdef
  have hEc : Continuous E := by rw [hEdef]; unfold eC; fun_prop
  have hW : ∀ y, s5fAvgWave Δ y = ((1 / (2 * Δ) : ℝ) : ℂ) * ∫ u in (-Δ)..Δ, g (y + u) := by
    intro y
    unfold s5fAvgWave
    congr 1
    rw [intervalIntegral.integral_comp_add_left (fun t => g t) y]
    simp only [hgdef, sub_eq_add_neg]
  have h1 : ∫ y in (0 : ℝ)..2, E y * s5fAvgWave Δ y
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
    · exact s5f_07e_g_meas.comp (measurable_fst.add measurable_snd)
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
      s5f_eC_add, s5f_07e_eC_int]
    norm_num
  have hinner : ∀ u : ℝ, ∫ y in (0 : ℝ)..2, E y * g (y + u)
      = eC (h / 2 * u) * ∫ y in (0 : ℝ)..2, E y * g y := by
    intro u
    have hEs : ∀ y, E y = eC (h / 2 * u) * E (y + u) := by
      intro y; simp only [hEdef]; rw [← s5f_eC_add]; congr 1; ring
    rw [← intervalIntegral.integral_const_mul]
    have : ∫ y in (0 : ℝ)..2, E y * g (y + u) = ∫ y in (0 : ℝ)..2, eC (h / 2 * u) * (E (y + u) * g (y + u)) := by
      apply intervalIntegral.integral_congr; intro y _; simp only; rw [hEs y]; ring
    rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (fun y => E y * g y) u, zero_add]
    congr 1
    have := hP.intervalIntegral_add_eq u 0
    rw [zero_add, add_comm] at this
    exact this
  show ∫ y in (0 : ℝ)..2, E y * s5fAvgWave Δ y = _
  rw [h1, hswap]
  congr 1
  simp only [hinner]
  rw [intervalIntegral.integral_mul_const]

/-- The Fourier coefficient of the square wave `(-1)^{⌊y⌋}` of period `2` at frequency `h/2`:
`2/(π i h) = (2/(π h)) (-i)` for odd `h`, `0` for even `h`. -/
theorem s5f_07d_wave_coeff (h : ℤ) :
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
`s5fAvgWave Δ y = (1/(2Δ)) ∫_{-Δ}^{Δ} (-1)^{⌊y + u⌋} du`, Fubini on `[0, 2] × [-Δ, Δ]` and the
period `2` of `(-1)^{⌊y⌋}` give that the coefficient of the average at frequency `h/2` is
`(1/(2Δ)) ∫_{-Δ}^{Δ} e(h u/2) du = sin(π h Δ)/(π h Δ)` times the coefficient of the wave. -/
theorem s5f_07d_average_multiplier (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (h : ℤ) :
    (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * s5fAvgWave Δ y
      = ((Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ) : ℝ) : ℂ) *
        ((1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋) := by
  rw [s5f_07e_key Δ hΔ₀ h]
  by_cases h0 : h = 0
  · have hw := s5f_07d_wave_coeff h
    rw [h0, if_neg (by simp : ¬ Odd (0 : ℤ))] at hw
    subst h0
    have hC : ∫ y in (0 : ℝ)..2, eC (-(((0 : ℤ) : ℝ) / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋ = 0 := by
      have := hw; simpa using this
    rw [hC]; simp
  · rw [s5f_07e_exp_avg h h0 Δ hΔ₀]
    have hΔ' : ((2 * Δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Δ : ℝ) ≠ 0)
    have : ((1 / (2 * Δ) : ℝ) : ℂ) * ((2 * Δ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
    linear_combination (((Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ) : ℝ) : ℂ) *
      ((1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * (-1 : ℂ) ^ ⌊y⌋)) * this


/-- `leaf_s5f_07c_coeff`, exact statement, from the multiplier leaf and `s5f_07d_wave_coeff`. -/
theorem s5f_07c_coeff (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (h : ℤ) :
    (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..2, eC (-(h / 2 * y)) * s5fAvgWave Δ y = s5fSqCoeff Δ h := by
  rw [s5f_07d_average_multiplier Δ hΔ₀ hΔ₁ h, s5f_07d_wave_coeff h]
  unfold s5fSqCoeff
  split_ifs
  · push_cast; ring
  · simp
end LeanLab.ExceptionalSet.U1539

namespace LeanLab.ExceptionalSet.Feed1122ParityCore

open LeanLab.ExceptionalSet.U1539

/-- The circle `ℝ / 2ℤ` of period two carries the Fourier theory used below. -/
local instance fact_two_pos_s5d : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩

/-- The averaged square wave is real. -/
theorem s5f_avg_im (A y : ℝ) : (s5fAvgWave A y).im = 0 := by
  unfold s5fAvgWave
  have : (fun t : ℝ => (-1 : ℂ) ^ ⌊t⌋) = fun t : ℝ => (((-1 : ℝ) ^ ⌊t⌋ : ℝ) : ℂ) := by
    funext t; push_cast; rfl
  rw [this, intervalIntegral.integral_ofReal, ← Complex.ofReal_mul, Complex.ofReal_im]

/-- Display (40): the coefficient of the averaged square wave is at most
`2 min(1, A ^ (-1) h ^ (-2))` for `h ≠ 0`. -/
theorem s5f_sq_le (A : ℝ) (hA : 0 < A) (h : ℤ) (hh : h ≠ 0) :
    ‖s5fSqCoeff A h‖ ≤ 2 * min 1 (1 / (A * (h : ℝ) ^ 2)) := by
  unfold s5fSqCoeff
  split_ifs with ho
  · rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    have hpi := Real.pi_gt_three
    have habs1 : 1 ≤ |(h : ℝ)| := by
      have : (1 : ℤ) ≤ |h| := Int.one_le_abs hh
      have h' : ((|h| : ℤ) : ℝ) = |(h : ℝ)| := by push_cast; rfl
      rw [← h']; exact_mod_cast this
    set x := Real.pi * h * A with hx
    have hx0 : x ≠ 0 := by rw [hx]; positivity
    have hxabs : |x| = Real.pi * |(h : ℝ)| * A := by
      rw [hx, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hA]
    have hsinc : |Real.sin x / x| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr hx0)]
      exact Real.abs_sin_le_abs
    have hsinc2 : |Real.sin x / x| ≤ 1 / (Real.pi * |(h : ℝ)| * A) := by
      rw [abs_div, hxabs]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (by positivity)
    rw [abs_mul]
    have hfirst : |2 / (Real.pi * h)| = 2 / (Real.pi * |(h : ℝ)|) := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    rw [hfirst]
    have hsq : (h : ℝ) ^ 2 = |(h : ℝ)| ^ 2 := (sq_abs _).symm
    rw [hsq]
    set a := |(h : ℝ)| with ha
    have ha0 : 0 < a := lt_of_lt_of_le one_pos habs1
    have hs0 : 0 ≤ |Real.sin x / x| := abs_nonneg _
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), mul_one]
    refine le_min ?_ ?_
    · calc 2 / (Real.pi * a) * |Real.sin x / x| ≤ 2 / (Real.pi * a) * 1 :=
            mul_le_mul_of_nonneg_left hsinc (by positivity)
        _ ≤ 2 := by
            rw [mul_one, div_le_iff₀ (by positivity)]; nlinarith
    · calc 2 / (Real.pi * a) * |Real.sin x / x|
            ≤ 2 / (Real.pi * a) * (1 / (Real.pi * a * A)) :=
            mul_le_mul_of_nonneg_left hsinc2 (by positivity)
        _ = 2 / (Real.pi ^ 2 * (A * a ^ 2)) := by field_simp
        _ ≤ 2 * (1 / (A * a ^ 2)) := by
            rw [mul_one_div]
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            have h0 : 0 < A * a ^ 2 := by positivity
            have hp2 : 1 < Real.pi ^ 2 := by nlinarith
            have := mul_lt_mul_of_pos_right hp2 h0
            linarith
  · simp only [norm_zero]; positivity

/-- PROVED by unit S5-17f, formerly a LEAF of class MEDIUM: P0082 page 370 display (40), the
trapezoid and its coefficients. The trapezoid is `(1 + W) / 2` with `W` the square wave averaged
over half width `A`, `s5fAvgWave`.
For `0 < A ≤ 1 / 4` there is a continuous function on the circle `ℝ / 2ℤ`, the period two
trapezoid, one on `[k + A, k + 1 - A]` for `k` even, zero there for `k` odd, linear on the
ramps of width `2 A` around the integers, with real values in `[0, 1]`, equal off the ramps to
the indicator of `⌊x⌋` even, whose Fourier coefficients satisfy
`|c_h| ≤ C min(1, A ^ (-1) h ^ (-2))`, by integrating by parts twice. -/
theorem leaf_trapezoid_circle :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 →
      ∃ f : C(AddCircle (2 : ℝ), ℂ), (∀ h : ℤ, ‖fourierCoeff f h‖ ≤ C * trapW A h) ∧
        (∀ y : AddCircle (2 : ℝ), (f y).im = 0 ∧ 0 ≤ (f y).re ∧ (f y).re ≤ 1) ∧
        ∀ x : ℝ, A ≤ Int.fract x → Int.fract x ≤ 1 - A →
          f (x : AddCircle (2 : ℝ)) = if Even ⌊x⌋ then 1 else 0 := by
  refine ⟨1, one_pos, fun A hA hA4 => ?_⟩
  have hp := s5f_07c_periodic A hA
  set F : C(AddCircle (2 : ℝ), ℂ) :=
    ⟨hp.lift, continuous_coinduced_dom.mpr (s5f_07c_continuous A hA)⟩ with hFdef
  have hfour : ∀ (n : ℤ) (x : ℝ), fourier n (x : AddCircle (2 : ℝ)) = eC (n / 2 * x) := by
    intro n x
    rw [fourier_coe_apply]
    unfold eC
    congr 1
    push_cast
    ring
  have hfc : ∀ n : ℤ, fourierCoeff F n = s5fSqCoeff A n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral F n 0, zero_add, ← s5f_07c_coeff A hA hA4 n,
      Complex.real_smul]
    congr 1
    · norm_num
    · apply intervalIntegral.integral_congr
      intro x _
      simp only [hFdef, ContinuousMap.coe_mk, Function.Periodic.lift_coe, smul_eq_mul]
      rw [hfour]
      congr 2
      push_cast
      ring
  have hFv : ∀ x : ℝ, F (x : AddCircle (2 : ℝ)) = s5fAvgWave A x := by
    intro x
    simp only [hFdef, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
  refine ⟨(1 / 2 : ℂ) • ((fourier 0 : C(AddCircle (2 : ℝ), ℂ)) + F), ?_, ?_, ?_⟩
  · intro h
    have hco : fourierCoeff (⇑((1 / 2 : ℂ) • ((fourier 0 : C(AddCircle (2 : ℝ), ℂ)) + F))) h
        = (1 / 2 : ℂ) * ((Pi.single (0 : ℤ) (1 : ℂ) : ℤ → ℂ) h + fourierCoeff F h) := by
      rw [ContinuousMap.coe_smul, fourierCoeff.const_smul, ContinuousMap.coe_add, fourierCoeff.add
        ((fourier 0 : C(AddCircle (2 : ℝ), ℂ)).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        (F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
        fourierCoeff_fourier, smul_eq_mul]
      rfl
    rw [hco, hfc, one_mul]
    unfold trapW
    by_cases h0 : h = 0
    · subst h0
      rw [if_pos rfl, Pi.single_eq_same]
      have : s5fSqCoeff A 0 = 0 := by
        unfold s5fSqCoeff; rw [if_neg (by simp)]
      rw [this, add_zero, mul_one, norm_div, norm_one, Complex.norm_ofNat]; norm_num
    · rw [if_neg h0, Pi.single_eq_of_ne h0, zero_add, norm_mul, norm_div, norm_one,
        Complex.norm_ofNat]
      have := s5f_sq_le A hA h h0
      linarith
  · intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hv : ((1 / 2 : ℂ) • ((fourier 0 : C(AddCircle (2 : ℝ), ℂ)) + F)) (x : AddCircle (2 : ℝ))
        = (1 / 2 : ℂ) * (1 + s5fAvgWave A x) := by
      rw [ContinuousMap.smul_apply, ContinuousMap.add_apply, fourier_zero, smul_eq_mul]
      exact congrArg _ (congrArg _ (hFv x))
    have hv' : ((1 / 2 : ℂ) • ((fourier 0 : C(AddCircle (2 : ℝ), ℂ)) + F))
        (QuotientAddGroup.mk x) = (1 / 2 : ℂ) * (1 + s5fAvgWave A x) := hv
    rw [hv']
    have him := s5f_avg_im A x
    have hre := Complex.abs_re_le_norm (s5fAvgWave A x)
    have hn := s5f_07b_avg_norm_le A x hA
    have hre' : |(s5fAvgWave A x).re| ≤ 1 := hre.trans hn
    rw [abs_le] at hre'
    refine ⟨?_, ?_, ?_⟩
    · simp [Complex.mul_im, him]
    · simp [Complex.mul_re, him]; linarith
    · simp [Complex.mul_re, him]; linarith
  · intro x h1 h2
    rw [ContinuousMap.smul_apply, ContinuousMap.add_apply, fourier_zero, smul_eq_mul, hFv,
      s5f_07b_avg_eq_wave A x hA h1 h2]
    split_ifs with he
    · rw [he.neg_one_zpow]; norm_num
    · rw [(Int.not_even_iff_odd.mp he).neg_one_zpow]; norm_num

/-- Proved: the weight `trapW` is summable over `ℤ`, from `leaf_trapezoid_weight_sums` at
`H = 1`. -/
theorem summable_trapW_s5 {A : ℝ} (hA : 0 < A) (hA4 : A ≤ 1 / 4) : Summable (trapW A) := by
  obtain ⟨C, _, hC⟩ := leaf_trapezoid_weight_sums
  obtain ⟨h1, h2⟩ := hC A hA hA4 1 le_rfl
  have hnn : ∀ h : ℤ, 0 ≤ trapW A h := by
    intro h
    unfold trapW
    split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one (by positivity)
  refine summable_of_sum_le (c := C * A ^ (-(1 / 2 : ℝ)) + C / (A * (1 : ℕ)))
    (fun h => hnn h) (fun u => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not u (fun h => h ∈ Finset.Icc (-((1 : ℕ) : ℤ)) (1 : ℕ))]
  refine add_le_add ((Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun h _ _ => hnn h)).trans h1)
    (h2 _ ?_)
  · intro h hh
    exact (Finset.mem_filter.1 hh).2
  · rw [Finset.disjoint_left]
    intro h hh
    exact (Finset.mem_filter.1 hh).2

/-- Proved: `leaf_trapezoid_fourier_series` verbatim, CONDITIONAL ON `leaf_trapezoid_circle`;
the convergence of the Fourier series is Mathlib's
`has_pointwise_sum_fourier_series_of_summable`. -/
theorem leaf_trapezoid_fourier_series_of_leaves :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 →
      ∃ c : ℤ → ℂ, (∀ h : ℤ, ‖c h‖ ≤ C * trapW A h) ∧
        ∀ x : ℝ, ∃ T : ℝ, 0 ≤ T ∧ T ≤ 1 ∧
          (A ≤ Int.fract x → Int.fract x ≤ 1 - A → (T : ℂ) = if Even ⌊x⌋ then 1 else 0) ∧
          HasSum (fun h : ℤ => c h * eC ((h : ℝ) / 2 * x)) (T : ℂ) := by
  obtain ⟨C, hC, hf⟩ := leaf_trapezoid_circle
  refine ⟨C, hC, fun A hA hA4 => ?_⟩
  obtain ⟨f, hcoef, hreal, hval⟩ := hf A hA hA4
  have hsum : Summable (fourierCoeff f) :=
    Summable.of_norm_bounded ((summable_trapW_s5 hA hA4).mul_left C) hcoef
  refine ⟨fourierCoeff f, hcoef, fun x => ?_⟩
  obtain ⟨him, hre0, hre1⟩ := hreal (x : AddCircle (2 : ℝ))
  have hT : (((f (x : AddCircle (2 : ℝ))).re : ℝ) : ℂ) = f (x : AddCircle (2 : ℝ)) :=
    Complex.ext (by simp) (by simp [him])
  refine ⟨(f (x : AddCircle (2 : ℝ))).re, hre0, hre1, fun h1 h2 => ?_, ?_⟩
  · rw [hT]; exact hval x h1 h2
  · rw [hT]
    have hp := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (2 : ℝ))
    refine hp.congr_fun (fun h => ?_)
    rw [smul_eq_mul, fourier_coe_apply]
    unfold eC
    congr 2
    push_cast
    ring

example : type_of% @leaf_trapezoid_fourier_series := leaf_trapezoid_fourier_series_of_leaves

end LeanLab.ExceptionalSet.Feed1122ParityCore

#print axioms LeanLab.ExceptionalSet.Feed1122ParityCore.leaf_trapezoid_circle
#print axioms LeanLab.ExceptionalSet.Feed1122ParityCore.summable_trapW_s5
#print axioms LeanLab.ExceptionalSet.Feed1122ParityCore.leaf_trapezoid_fourier_series_of_leaves
