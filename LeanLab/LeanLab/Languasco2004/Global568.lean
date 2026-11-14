/-
Jia 1996 page 280, the third, fifth and sixth numerical components.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The factor 0.5607 is the cited global Buchstab lower bound from Lemma 20.
This file proves numerical bounds for that explicit rational minorant only.
-/
import LeanLab.Languasco2004.Numeric548
import LeanLab.Languasco2004.MovingIntegral548
namespace LeanLab.Languasco2004.Global568
open Real Set intervalIntegral Numeric548 MovingIntegral548
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Page 280 numerical support: eight geometric terms approximate a reciprocal from below. -/
def invPoly7 (x c : ℝ) : ℝ :=
  (1 + (1 - x / c) + (1 - x / c)^2 + (1 - x / c)^3 +
    (1 - x / c)^4 + (1 - x / c)^5 + (1 - x / c)^6 + (1 - x / c)^7) / c

/-- Page 280 numerical support: the exact eighth power remainder is nonnegative. -/
theorem invPoly7_bounds (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hxc : x ≤ c) :
    0 ≤ invPoly7 x c ∧ invPoly7 x c ≤ 1 / x := by
  have hz : 0 ≤ 1 - x / c := sub_nonneg.mpr ((div_le_one hc).mpr hxc)
  have he : invPoly7 x c * x = 1 - (1 - x / c)^8 := by
    unfold invPoly7
    field_simp
    ring
  constructor
  · unfold invPoly7
    positivity
  · apply (le_div_iff₀ hx).mpr
    nlinarith [pow_nonneg hz 8]

/-- Page 280: a polynomial minorant of 0.5607 divided by t times u squared. -/
def globalPoly (T U t u : ℝ) : ℝ :=
  0.5607 * invPoly5 t T * (invPoly7 u U)^2

/-- Page 280: reciprocal bounds give the pointwise numerical minorant. -/
theorem globalPoly_le (T U t u : ℝ) (ht : 0 < t) (hu : 0 < u)
    (hT : 0 < T) (hU : 0 < U) (htT : t ≤ T) (huU : u ≤ U) :
    globalPoly T U t u ≤ 0.5607 / (t * u^2) := by
  obtain ⟨ht0, ht1⟩ := invPoly5_bounds t T ht hT htT
  obtain ⟨hu0, hu1⟩ := invPoly7_bounds u U hu hU huU
  have hs := pow_le_pow_left₀ hu0 hu1 2
  have hp := mul_le_mul ht1 hs (sq_nonneg _) (by positivity)
  have h := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 0.5607)
  calc globalPoly T U t u ≤ 0.5607 * (1 / t * (1 / u)^2) := by
         simpa only [globalPoly, mul_assoc] using h
       _ = _ := by field_simp

/-- LEAF. Page 280: exact polynomial integration for the third component. -/
theorem global3_polynomial :
    (0.0660467 : ℝ) ≤ ∫ t in (619 / 2349 : ℝ)..(31 / 99),
      ∫ u in (701 / 1566 - t)..((1 - t) / 4), globalPoly (31 / 99) (865 / 4698) t u := by sorry

/-- LEAF. Page 280: exact polynomial integration for the fifth component. -/
theorem global5_polynomial :
    (0.0514082 : ℝ) ≤ ∫ t in (31 / 99 : ℝ)..(859 / 2610),
      ∫ u in (701 / 1566 - t)..(89 / 201 - 58 / 67 * t), globalPoly (859 / 2610) (17 / 99) t u := by sorry

/-- LEAF. Page 280: exact polynomial integration for the sixth component. -/
theorem global6_polynomial :
    (0.08440004 : ℝ) ≤ ∫ t in (859 / 2610 : ℝ)..(10 / 27),
      ∫ u in (16 / 135 : ℝ)..(89 / 201 - 58 / 67 * t), globalPoly (10 / 27) (476 / 3015) t u := by sorry

/-- LEAF. Page 280 numerical support: the moving rational kernel is continuous on positive rectangles. -/
theorem global_inner_continuousOn (a b c d : ℝ) (L U : ℝ → ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hL : Continuous L) (hU : Continuous U)
    (hbound : ∀ t ∈ Icc a b, c ≤ L t ∧ L t ≤ U t ∧ U t ≤ d) :
    ContinuousOn (fun t : ℝ => ∫ u in L t..U t, 0.5607 / (t * u^2)) (Icc a b) := by sorry

/-- Page 280 numerical support: the explicit polynomial inner integral is continuous. -/
theorem global_poly_inner_continuous (T U : ℝ) (L V : ℝ → ℝ)
    (hL : Continuous L) (hV : Continuous V) :
    Continuous (fun t : ℝ => ∫ u in L t..V t, globalPoly T U t u) := by
  have hc : Continuous (Function.uncurry (globalPoly T U)) := by
    unfold globalPoly invPoly5 invPoly7
    fun_prop
  have hv := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc hV
  have hl := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc hL
  have hp (t : ℝ) : Continuous (globalPoly T U t) := by
    unfold globalPoly invPoly5 invPoly7
    fun_prop
  have he : (fun t : ℝ => ∫ u in L t..V t, globalPoly T U t u) =
      fun t : ℝ => (∫ u in (0 : ℝ)..V t, globalPoly T U t u) -
        (∫ u in (0 : ℝ)..L t, globalPoly T U t u) := by
    funext t
    exact (integral_interval_sub_left ((hp t).intervalIntegrable _ _)
      ((hp t).intervalIntegrable _ _)).symm
  rw [he]
  exact hv.sub hl

/-- Page 280: integrate the polynomial minorant over any positive source strip. -/
theorem global_integral_compare (a b c T U : ℝ) (L V : ℝ → ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcU : c ≤ U)
    (hT : b ≤ T) (hL : Continuous L) (hV : Continuous V)
    (hbound : ∀ t ∈ Icc a b, c ≤ L t ∧ L t ≤ V t ∧ V t ≤ U) :
    (∫ t in a..b, ∫ u in L t..V t, globalPoly T U t u) ≤
      ∫ t in a..b, ∫ u in L t..V t, 0.5607 / (t * u^2) := by
  apply integral_mono_on hab ((global_poly_inner_continuous T U L V hL hV).intervalIntegrable _ _)
    ((global_inner_continuousOn a b c U L V ha hab hc hcU
      hL hV hbound).intervalIntegrable_of_Icc hab)
  intro t ht
  obtain ⟨hcL, hLV, hVU⟩ := hbound t ht
  have ht0 : 0 < t := ha.trans_le ht.1
  have hu0 (u : ℝ) (hu : u ∈ Icc (L t) (V t)) : 0 < u := hc.trans_le (hcL.trans hu.1)
  have hp : IntervalIntegrable (globalPoly T U t) MeasureTheory.volume (L t) (V t) := by
    apply Continuous.intervalIntegrable
    unfold globalPoly invPoly5 invPoly7
    fun_prop
  have hr : IntervalIntegrable (fun u : ℝ => 0.5607 / (t * u^2)) MeasureTheory.volume (L t) (V t) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hLV
    apply continuousOn_const.div (by fun_prop)
    intro u hu
    exact (mul_pos ht0 (sq_pos_of_pos (hu0 u hu))).ne'
  exact integral_mono_on hLV hp hr (fun u hu => globalPoly_le T U t u ht0 (hu0 u hu)
    (ha.trans_le (hab.trans hT)) (hc.trans_le hcU) (ht.2.trans hT) (hu.2.trans hVU))

/-- Page 280: the third rational minorant integral reaches its printed coefficient. -/
theorem global3_lower :
    (0.0660467 : ℝ) ≤ ∫ t in (619 / 2349 : ℝ)..(31 / 99),
      ∫ u in (701 / 1566 - t)..((1 - t) / 4), 0.5607 / (t * u^2) := by
  apply global3_polynomial.trans
  apply global_integral_compare (619 / 2349) (31 / 99) (16 / 135) (31 / 99) (865 / 4698)
    (fun t => 701 / 1566 - t) (fun t => (1 - t) / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by fun_prop) (by fun_prop)
  intro t ht
  obtain ⟨hl, hu⟩ := ht
  constructor
  · linarith
  constructor <;> linarith

/-- Page 280: the fifth rational minorant integral reaches its printed coefficient. -/
theorem global5_lower :
    (0.0514082 : ℝ) ≤ ∫ t in (31 / 99 : ℝ)..(859 / 2610),
      ∫ u in (701 / 1566 - t)..(89 / 201 - 58 / 67 * t), 0.5607 / (t * u^2) := by
  apply global5_polynomial.trans
  apply global_integral_compare (31 / 99) (859 / 2610) (16 / 135) (859 / 2610) (17 / 99)
    (fun t => 701 / 1566 - t) (fun t => 89 / 201 - 58 / 67 * t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by fun_prop) (by fun_prop)
  intro t ht
  obtain ⟨hl, hu⟩ := ht
  constructor
  · linarith
  constructor <;> linarith

/-- Page 280: the sixth rational minorant integral reaches its printed coefficient. -/
theorem global6_lower :
    (0.08440004 : ℝ) ≤ ∫ t in (859 / 2610 : ℝ)..(10 / 27),
      ∫ u in (16 / 135 : ℝ)..(89 / 201 - 58 / 67 * t), 0.5607 / (t * u^2) := by
  apply global6_polynomial.trans
  apply global_integral_compare (859 / 2610) (10 / 27) (16 / 135) (10 / 27) (476 / 3015)
    (fun _ => 16 / 135) (fun t => 89 / 201 - 58 / 67 * t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by fun_prop) (by fun_prop)
  intro t ht
  obtain ⟨hl, hu⟩ := ht
  constructor
  · linarith
  constructor <;> linarith

#print axioms invPoly7_bounds
#print axioms globalPoly_le
#print axioms global3_polynomial
#print axioms global5_polynomial
#print axioms global6_polynomial
#print axioms global_inner_continuousOn
#print axioms global_poly_inner_continuous
#print axioms global_integral_compare
#print axioms global3_lower
#print axioms global5_lower
#print axioms global6_lower
end
end LeanLab.Languasco2004.Global568
