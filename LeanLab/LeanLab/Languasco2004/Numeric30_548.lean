/-
Jia 1996 pages 281 and 282, the first integral in Lemma 27.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The numerical coefficient is independent of the OPEN exceptional prime estimates.
-/
import LeanLab.Languasco2004.LogKernel548
import LeanLab.Languasco2004.MovingIntegral548

namespace LeanLab.Languasco2004.Numeric30_548
open Real Set intervalIntegral Kernel548 LogKernel548 MovingIntegral548 BuchstabInitial316
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Page 281 numerical support: four geometric terms enclose a positive reciprocal. -/
def invPoly3 (x c : ℝ) : ℝ :=
  (1 + (1 - x / c) + (1 - x / c)^2 + (1 - x / c)^3) / c

/-- Page 281 numerical support: the fourth power remainder is nonnegative. -/
theorem invPoly3_bounds (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hxc : x ≤ c) :
    0 ≤ invPoly3 x c ∧ invPoly3 x c ≤ 1 / x := by
  have hz : 0 ≤ 1 - x / c := sub_nonneg.mpr ((div_le_one hc).mpr hxc)
  have he : invPoly3 x c * x = 1 - (1 - x / c)^4 := by
    unfold invPoly3
    field_simp
    ring
  constructor
  · unfold invPoly3
    positivity
  · apply (le_div_iff₀ hx).mpr
    nlinarith [pow_nonneg hz 4]

/-- Page 281: a polynomial minorant using the rational logarithmic chord. -/
def polynomial30 (t u : ℝ) : ℝ :=
  0.6395421 * (invPoly3 t (1649 / 4752) * invPoly3 u (17 / 99) * invPoly3 (1 - t - u) (1 / 2)) +
  0.5268025 * (1 - t - 2 * u) *
    (invPoly3 t (1649 / 4752) * invPoly3 u (17 / 99)^2 * invPoly3 (1 - t - u) (1 / 2))

/-- Page 281: the polynomial minorizes the full logarithmic kernel on D30. -/
theorem polynomial30_le (t u : ℝ) (htl : 34 / 99 ≤ t) (htu : t ≤ 1649 / 4752)
    (hul : 85 / 99 - 2 * t ≤ u) (huu : u ≤ 85 / 147 - 58 / 49 * t) :
    polynomial30 t u ≤
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, _, _⟩ := region30_argument t u htl htu hul huu
  have huB : u ≤ 17 / 99 := by linarith
  have hvB : 1 - t - u ≤ 1 / 2 := by linarith
  have hnum : 0 ≤ 1 - t - 2 * u := by linarith
  obtain ⟨ht0, htB⟩ := invPoly3_bounds t (1649 / 4752) ht (by norm_num) htu
  obtain ⟨hu0, huB⟩ := invPoly3_bounds u (17 / 99) hu (by norm_num) huB
  obtain ⟨hv0, hvB⟩ := invPoly3_bounds (1 - t - u) (1 / 2) hv (by norm_num) hvB
  have htu1 := mul_le_mul htB huB hu0 (by positivity : (0 : ℝ) ≤ 1 / t)
  have h1 := mul_le_mul htu1 hvB hv0 (by positivity : (0 : ℝ) ≤ 1 / t * (1 / u))
  have huSq : invPoly3 u (17 / 99)^2 ≤ (1 / u)^2 := by nlinarith
  have htu2 := mul_le_mul htB huSq (sq_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / t)
  have h2 := mul_le_mul htu2 hvB hv0 (by positivity : (0 : ℝ) ≤ 1 / t * (1 / u)^2)
  have hsum := add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 0.6395421))
    (mul_le_mul_of_nonneg_left h2
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.5268025) hnum))
  have hrat : polynomial30 t u ≤
      0.6395421 / (t * u * (1 - t - u)) +
      0.5268025 * (1 - t - 2 * u) / (t * u ^ 2 * (1 - t - u)) := by
    calc polynomial30 t u ≤
          0.6395421 * (1 / t * (1 / u) * (1 / (1 - t - u))) +
          0.5268025 * (1 - t - 2 * u) * (1 / t * (1 / u)^2 * (1 / (1 - t - u))) := hsum
         _ = _ := by field_simp
  exact hrat.trans (region30_kernel_lower t u htl htu hul huu)

/-- Page 282: exact polynomial integration exceeds the printed first coefficient. -/
theorem polynomial30_integral :
    (0.0003031 : ℝ) ≤ ∫ t in (34 / 99 : ℝ)..(1649 / 4752),
      ∫ u in (85 / 99 - 2 * t)..(85 / 147 - 58 / 49 * t), polynomial30 t u := by
  unfold polynomial30 invPoly3
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

/-- Page 281: the source logarithmic inner integral. -/
def inner30 (t : ℝ) : ℝ :=
  ∫ u in (85 / 99 - 2 * t)..(85 / 147 - 58 / 49 * t),
    (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u))

/-- Page 281: the logarithmic inner integral is continuous on its source t interval. -/
theorem inner30_continuousOn : ContinuousOn inner30 (Icc (34 / 99) (1649 / 4752)) := by
  let R := Icc (34 / 99 : ℝ) (1649 / 4752) ×ˢ
    Icc (85 / 99 - 2 * (1649 / 4752 : ℝ)) (17 / 99)
  have ht (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.1 := by linarith [hz.1.1]
  have hu (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.2 := by linarith [hz.2.1]
  have hv (z : ℝ × ℝ) (hz : z ∈ R) : 0 < 1 - z.1 - z.2 := by
    linarith [hz.1.2, hz.2.2]
  have harg (z : ℝ × ℝ) (hz : z ∈ R) : 0 < (1 - z.1) / z.2 - 2 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ (hu z hz)).mpr
    linarith [hz.1.2, hz.2.2]
  have hrat : ContinuousOn (fun z : ℝ × ℝ => (1 - z.1) / z.2 - 2) R :=
    ((continuousOn_const.sub continuous_fst.continuousOn).div continuous_snd.continuousOn
      (fun z hz => (hu z hz).ne')).sub continuousOn_const
  have hnum : ContinuousOn (fun z : ℝ × ℝ => 1 + Real.log ((1 - z.1) / z.2 - 2)) R :=
    continuousOn_const.add (hrat.log (fun z hz => (harg z hz).ne'))
  have hden : ContinuousOn (fun z : ℝ × ℝ => z.1 * z.2 * (1 - z.1 - z.2)) R := by fun_prop
  have hc := hnum.div hden (fun z hz => (mul_pos (mul_pos (ht z hz) (hu z hz)) (hv z hz)).ne')
  apply moving_integral_continuousOn
    (fun t u : ℝ => (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)))
    (34 / 99) (1649 / 4752) (85 / 99 - 2 * (1649 / 4752)) (17 / 99)
    (fun t => 85 / 99 - 2 * t) (fun t => 85 / 147 - 58 / 49 * t)
    (by norm_num) (by norm_num) hc (by fun_prop) (by fun_prop)
  intro t ht
  have := ht.1
  have := ht.2
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Page 281: the polynomial inner integral is continuous for every real t. -/
theorem polynomial_inner_continuous : Continuous (fun t : ℝ =>
    ∫ u in (85 / 99 - 2 * t)..(85 / 147 - 58 / 49 * t), polynomial30 t u) := by
  have hc : Continuous (Function.uncurry polynomial30) := by
    unfold polynomial30 invPoly3
    fun_prop
  have hU := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc
    (show Continuous (fun t : ℝ => 85 / 147 - 58 / 49 * t) by fun_prop)
  have hL := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc
    (show Continuous (fun t : ℝ => 85 / 99 - 2 * t) by fun_prop)
  have hp (t : ℝ) : Continuous (polynomial30 t) := by
    unfold polynomial30 invPoly3
    fun_prop
  have he : (fun t : ℝ => ∫ u in (85 / 99 - 2 * t)..(85 / 147 - 58 / 49 * t), polynomial30 t u) =
      fun t : ℝ => (∫ u in (0 : ℝ)..(85 / 147 - 58 / 49 * t), polynomial30 t u) -
      (∫ u in (0 : ℝ)..(85 / 99 - 2 * t), polynomial30 t u) := by
    funext t
    exact (integral_interval_sub_left ((hp t).intervalIntegrable _ _)
      ((hp t).intervalIntegrable _ _)).symm
  rw [he]
  exact hU.sub hL

/-- Page 282: the complete logarithmic integral has a reserve above 0.000303. -/
theorem region30_numeric_margin :
    (0.0003031 : ℝ) ≤ ∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t := by
  have hinner (t : ℝ) (ht : t ∈ Icc (34 / 99 : ℝ) (1649 / 4752)) :
      (∫ u in (85 / 99 - 2 * t)..(85 / 147 - 58 / 49 * t), polynomial30 t u) ≤ inner30 t := by
    have hab : 85 / 99 - 2 * t ≤ 85 / 147 - 58 / 49 * t := by linarith [ht.1]
    have hp : IntervalIntegrable (polynomial30 t) MeasureTheory.volume
        (85 / 99 - 2 * t) (85 / 147 - 58 / 49 * t) := by
      apply Continuous.intervalIntegrable
      unfold polynomial30 invPoly3
      fun_prop
    have hr : IntervalIntegrable
        (fun u : ℝ => (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)))
        MeasureTheory.volume (85 / 99 - 2 * t) (85 / 147 - 58 / 49 * t) := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      have hu (u : ℝ) (hu : u ∈ Icc (85 / 99 - 2 * t) (85 / 147 - 58 / 49 * t)) : 0 < u := by
        linarith [ht.2, hu.1]
      have hv (u : ℝ) (hu : u ∈ Icc (85 / 99 - 2 * t) (85 / 147 - 58 / 49 * t)) : 0 < 1 - t - u := by
        linarith [ht.2, hu.2]
      have harg (u : ℝ) (hu : u ∈ Icc (85 / 99 - 2 * t) (85 / 147 - 58 / 49 * t)) :
          (1 - t) / u - 2 ≠ 0 := by
        have h := (region30_log_argument t u ht.1 ht.2 hu.1 hu.2).1
        have he : (1 - t - 2 * u) / u = (1 - t) / u - 2 := by
          have hu0 : 0 < u := by linarith [ht.2, hu.1]
          field_simp [hu0.ne']
        rw [he] at h
        linarith
      have hc : ContinuousOn (fun u : ℝ => (1 - t) / u - 2)
          (Icc (85 / 99 - 2 * t) (85 / 147 - 58 / 49 * t)) :=
        ((continuousOn_const.sub continuousOn_const).div continuousOn_id
        (fun u h => (hu u h).ne')).sub continuousOn_const
      exact (continuousOn_const.add (hc.log harg)).div
        (by fun_prop) (fun u h => (mul_pos (mul_pos (by linarith [ht.1]) (hu u h)) (hv u h)).ne')
    exact integral_mono_on hab hp hr
      (fun u hu => polynomial30_le t u ht.1 ht.2 hu.1 hu.2)
  have hm := integral_mono_on (by norm_num : (34 / 99 : ℝ) ≤ 1649 / 4752)
    (polynomial_inner_continuous.intervalIntegrable _ _)
    (inner30_continuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num)) hinner
  exact polynomial30_integral.trans hm

/-- Pages 281 and 282: the complete first Buchstab integral is at least 0.000303. -/
theorem region30_buchstab_lower :
    (0.000303 : ℝ) ≤ ∫ t in (34 / 99 : ℝ)..(1649 / 4752),
      ∫ u in (85 / 99 - 2 * t)..(85 / 147 - 58 / 49 * t),
        buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) := by
  have he : (∫ t in (34 / 99 : ℝ)..(1649 / 4752),
      ∫ u in (85 / 99 - 2 * t)..(85 / 147 - 58 / 49 * t),
        buchstabInitial ((1 - t - u) / u) / (t * u ^ 2)) =
      ∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    apply integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith [ht.1] :
      85 / 99 - 2 * t ≤ 85 / 147 - 58 / 49 * t)] at hu
    exact Kernel548.region30_kernel t u ht.1 ht.2 hu.1 hu.2
  rw [he]
  linarith [region30_numeric_margin]

#print axioms invPoly3_bounds
#print axioms polynomial30_le
#print axioms polynomial30_integral
#print axioms inner30_continuousOn
#print axioms polynomial_inner_continuous
#print axioms region30_numeric_margin
#print axioms region30_buchstab_lower
end
end LeanLab.Languasco2004.Numeric30_548
