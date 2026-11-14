/-
Jia 1996 pages 275 and 277, first integral in Lemma 25.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
A polynomial enclosure certifies the numerical integral only.
The exceptional prime estimate remains OPEN.
-/
import LeanLab.Languasco2004.Integral548

namespace LeanLab.Languasco2004.Numeric548
open Real intervalIntegral Kernel548 Integral548 BuchstabInitial316
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Page 275 integral support: six geometric terms enclose a positive reciprocal. -/
def invPoly5 (x c : ℝ) : ℝ :=
  (1 + (1 - x / c) + (1 - x / c)^2 + (1 - x / c)^3 +
    (1 - x / c)^4 + (1 - x / c)^5) / c

/-- Page 275 integral support: the geometric remainder has the correct sign. -/
theorem invPoly5_bounds (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hxc : x ≤ c) :
    0 ≤ invPoly5 x c ∧ invPoly5 x c ≤ 1 / x := by
  have hz : 0 ≤ 1 - x / c := sub_nonneg.mpr ((div_le_one hc).mpr hxc)
  have he : invPoly5 x c * x = 1 - (1 - x / c)^6 := by
    unfold invPoly5
    field_simp
    ring
  constructor
  · unfold invPoly5
    positivity
  · apply (le_div_iff₀ hx).mpr
    nlinarith [pow_nonneg hz 6]

/-- Page 275: a polynomial minorant of the complete D47 rational kernel. -/
def polynomial47 (t u : ℝ) : ℝ :=
  invPoly5 t (34 / 81) * invPoly5 u (53 / 216) * invPoly5 (1 - t - u) (10 / 27)

/-- Page 275: the polynomial is a pointwise lower bound on the source region. -/
theorem polynomial47_le (t u : ℝ) (htl : 11 / 27 ≤ t) (htu : t ≤ 34 / 81)
    (hul : 17 / 12 - 23 / 8 * t ≤ u) (huu : u ≤ 25 / 72 - t / 4) :
    polynomial47 t u ≤ 1 / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, _, _⟩ := region47_argument t u htl htu hul huu
  have huB : u ≤ 53 / 216 := by linarith
  have hvB : 1 - t - u ≤ 10 / 27 := by linarith
  obtain ⟨ht0, htB⟩ := invPoly5_bounds t (34 / 81) ht (by norm_num) htu
  obtain ⟨hu0, huB⟩ := invPoly5_bounds u (53 / 216) hu (by norm_num) huB
  obtain ⟨hv0, hvB⟩ := invPoly5_bounds (1 - t - u) (10 / 27) hv (by norm_num) hvB
  have htu := mul_le_mul htB huB hu0 (by positivity : (0 : ℝ) ≤ 1 / t)
  have hall := mul_le_mul htu hvB hv0 (by positivity : (0 : ℝ) ≤ 1 / t * (1 / u))
  calc polynomial47 t u ≤ 1 / t * (1 / u) * (1 / (1 - t - u)) := hall
       _ = 1 / (t * u * (1 - t - u)) := by
         simp only [one_div, mul_inv_rev]
         ring

/-- Page 277: exact polynomial integration reaches the printed first coefficient. -/
theorem polynomial47_integral :
    (0.0058884 : ℝ) ≤
      ∫ t in (11 / 27 : ℝ)..(34 / 81),
        ∫ u in (17 / 12 - 23 / 8 * t)..(25 / 72 - t / 4), polynomial47 t u := by
  unfold polynomial47 invPoly5
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

/-- Page 275: the polynomial inner integral has continuously moving endpoints. -/
def polynomialInner47 (t : ℝ) : ℝ :=
  ∫ u in (17 / 12 - 23 / 8 * t)..(25 / 72 - t / 4), polynomial47 t u

/-- Page 275: polynomial continuity supplies the outer integrability premise. -/
theorem polynomialInner47_continuous : Continuous polynomialInner47 := by
  have hc : Continuous (Function.uncurry polynomial47) := by
    unfold polynomial47 invPoly5
    fun_prop
  have hU := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc
    (show Continuous (fun t : ℝ => 25 / 72 - t / 4) by fun_prop)
  have hL := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc
    (show Continuous (fun t : ℝ => 17 / 12 - 23 / 8 * t) by fun_prop)
  have hp (t : ℝ) : Continuous (polynomial47 t) := by
    unfold polynomial47 invPoly5
    fun_prop
  have he : polynomialInner47 = fun t : ℝ =>
      (∫ u in (0 : ℝ)..(25 / 72 - t / 4), polynomial47 t u) -
      (∫ u in (0 : ℝ)..(17 / 12 - 23 / 8 * t), polynomial47 t u) := by
    funext t
    exact (integral_interval_sub_left ((hp t).intervalIntegrable _ _)
      ((hp t).intervalIntegrable _ _)).symm
  rw [he]
  exact hU.sub hL

/-- Page 275: the exact source integral has a strict reserve above the printed coefficient. -/
theorem region47_numeric_margin :
    (0.0058884 : ℝ) ≤ ∫ t in (11 / 27 : ℝ)..(34 / 81), inner47 t := by
  have hinner (t : ℝ) (ht : t ∈ Set.Icc (11 / 27 : ℝ) (34 / 81)) :
      polynomialInner47 t ≤ inner47 t := by
    have hab : 17 / 12 - 23 / 8 * t ≤ 25 / 72 - t / 4 := by linarith [ht.1]
    have hp : IntervalIntegrable (polynomial47 t) MeasureTheory.volume
        (17 / 12 - 23 / 8 * t) (25 / 72 - t / 4) := by
      apply Continuous.intervalIntegrable
      unfold polynomial47 invPoly5
      fun_prop
    have hr := rational_kernel_integrable t (17 / 12 - 23 / 8 * t)
      (25 / 72 - t / 4) (by linarith [ht.1]) hab
      (by linarith [ht.2]) (by linarith [ht.2])
    exact integral_mono_on hab hp hr
      (fun u hu => polynomial47_le t u ht.1 ht.2 hu.1 hu.2)
  have hm := integral_mono_on (by norm_num : (11 / 27 : ℝ) ≤ 34 / 81)
    (polynomialInner47_continuous.intervalIntegrable _ _)
    (inner47_continuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num)) hinner
  exact polynomial47_integral.trans hm

/-- Pages 275 and 277: the complete first Buchstab integral exceeds 0.005888.
This numerical estimate has no prime distribution or exceptional set premise. -/
theorem region47_buchstab_lower :
    (0.005888 : ℝ) ≤ ∫ t in (11 / 27 : ℝ)..(34 / 81),
      ∫ u in (17 / 12 - 23 / 8 * t)..(25 / 72 - t / 4),
        buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) := by
  have he : (∫ t in (11 / 27 : ℝ)..(34 / 81),
      ∫ u in (17 / 12 - 23 / 8 * t)..(25 / 72 - t / 4),
        buchstabInitial ((1 - t - u) / u) / (t * u ^ 2)) =
      ∫ t in (11 / 27 : ℝ)..(34 / 81), inner47 t := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    apply integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith [ht.1] :
      17 / 12 - 23 / 8 * t ≤ 25 / 72 - t / 4)] at hu
    exact Kernel548.region47_kernel t u ht.1 ht.2 hu.1 hu.2
  rw [he]
  linarith [region47_numeric_margin]

#print axioms invPoly5_bounds
#print axioms polynomial47_le
#print axioms polynomial47_integral
#print axioms polynomialInner47_continuous
#print axioms region47_numeric_margin
#print axioms region47_buchstab_lower
end
end LeanLab.Languasco2004.Numeric548
