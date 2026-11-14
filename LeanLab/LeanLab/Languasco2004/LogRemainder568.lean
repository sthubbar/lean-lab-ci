/-
Jia 1996 pages 279 and 280, the logarithmic components of Lemma 26.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Kernel568
import LeanLab.Languasco2004.Global568
namespace LeanLab.Languasco2004.LogRemainder568
open Real Set intervalIntegral Kernel568 Global568 Numeric548 Numeric30_548 MovingIntegral548
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Pages 279 and 280 numerical support: four positive logarithm series terms. -/
theorem log_four_terms (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) :
    2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7 ≤ Real.log ((1 + z) / (1 - z)) := by
  have h := Real.sum_range_le_log_div hz hz1 4
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Pages 279 and 280: a polynomial minorant for each logarithmic remainder component. -/
def logPoly (T U V t u : ℝ) : ℝ :=
  let v := invPoly3 (1 - t - u) V
  let z := (1 - t - 3 * u) * v
  invPoly5 t T * invPoly7 u U * v * (1 + 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7)

/-- LEAF. Pages 279 and 280: the source logarithmic kernel exceeds this polynomial. -/
theorem logPoly_le (T U V t u : ℝ)
    (ht : 0 < t) (hu : 0 < u) (hv : 0 < 1 - t - u) (ha : 0 ≤ 1 - t - 3 * u)
    (hT : 0 < T) (hU : 0 < U) (hV : 0 < V)
    (htT : t ≤ T) (huU : u ≤ U) (hvV : 1 - t - u ≤ V) :
    logPoly T U V t u ≤ (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by sorry

/-- LEAF. Pages 279 and 280: continuity of the logarithmic inner integral on a positive rectangle. -/
theorem log_inner_continuousOn (a b c d : ℝ) (L U : ℝ → ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hbd : b + 2 * d < 1)
    (hL : Continuous L) (hU : Continuous U)
    (hbound : ∀ t ∈ Icc a b, c ≤ L t ∧ L t ≤ U t ∧ U t ≤ d) :
    ContinuousOn (fun t : ℝ => ∫ u in L t..U t,
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u))) (Icc a b) := by sorry

/-- Pages 279 and 280: polynomial inner integrals have continuous moving endpoints. -/
theorem log_poly_inner_continuous (T U V : ℝ) (L W : ℝ → ℝ)
    (hL : Continuous L) (hW : Continuous W) :
    Continuous (fun t : ℝ => ∫ u in L t..W t, logPoly T U V t u) := by
  have hc : Continuous (Function.uncurry (logPoly T U V)) := by
    unfold logPoly invPoly3 invPoly5 invPoly7
    fun_prop
  have hw := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc hW
  have hl := continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hc hL
  have hp (t : ℝ) : Continuous (logPoly T U V t) := by
    unfold logPoly invPoly3 invPoly5 invPoly7
    fun_prop
  have he : (fun t : ℝ => ∫ u in L t..W t, logPoly T U V t u) =
      fun t : ℝ => (∫ u in (0 : ℝ)..W t, logPoly T U V t u) -
        (∫ u in (0 : ℝ)..L t, logPoly T U V t u) := by
    funext t
    exact (integral_interval_sub_left ((hp t).intervalIntegrable _ _)
      ((hp t).intervalIntegrable _ _)).symm
  rw [he]
  exact hw.sub hl

/-- Pages 279 and 280: integrate the logarithmic polynomial minorant on a source strip. -/
theorem log_integral_compare (a b c d V : ℝ) (L W : ℝ → ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hV : 0 < V)
    (hbd : b + 2 * d < 1) (hL : Continuous L) (hW : Continuous W)
    (hbound : ∀ t ∈ Icc a b, c ≤ L t ∧ L t ≤ W t ∧ W t ≤ d)
    (hkernel : ∀ t ∈ Icc a b, ∀ u ∈ Icc (L t) (W t),
      0 ≤ 1 - t - 3 * u ∧ 1 - t - u ≤ V) :
    (∫ t in a..b, ∫ u in L t..W t, logPoly b d V t u) ≤
      ∫ t in a..b, ∫ u in L t..W t,
        (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  apply integral_mono_on hab ((log_poly_inner_continuous b d V L W hL hW).intervalIntegrable _ _)
    ((log_inner_continuousOn a b c d L W ha hab hc hcd hbd
      hL hW hbound).intervalIntegrable_of_Icc hab)
  intro t ht
  obtain ⟨hcL, hLW, hWd⟩ := hbound t ht
  have ht0 : 0 < t := ha.trans_le ht.1
  have hu0 (u : ℝ) (hu : u ∈ Icc (L t) (W t)) : 0 < u := hc.trans_le (hcL.trans hu.1)
  have hv0 (u : ℝ) (hu : u ∈ Icc (L t) (W t)) : 0 < 1 - t - u := by
    linarith [ht.2, hu.2.trans hWd, hu0 u hu]
  have harg (u : ℝ) (hu : u ∈ Icc (L t) (W t)) : (1 - t) / u - 2 ≠ 0 := by
    have hp : 0 < (1 - t) / u - 2 := by
      apply sub_pos.mpr
      apply (lt_div_iff₀ (hu0 u hu)).mpr
      linarith [ht.2, hu.2.trans hWd]
    exact hp.ne'
  have hp : IntervalIntegrable (logPoly b d V t) MeasureTheory.volume (L t) (W t) := by
    apply Continuous.intervalIntegrable
    unfold logPoly invPoly3 invPoly5 invPoly7
    fun_prop
  have hr : IntervalIntegrable (fun u : ℝ =>
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u))) MeasureTheory.volume (L t) (W t) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hLW
    have hrat : ContinuousOn (fun u : ℝ => (1 - t) / u - 2) (Icc (L t) (W t)) :=
      ((continuousOn_const.sub continuousOn_const).div continuousOn_id
        (fun u hu => (hu0 u hu).ne')).sub continuousOn_const
    exact (continuousOn_const.add (hrat.log harg)).div (by fun_prop)
      (fun u hu => (mul_pos (mul_pos ht0 (hu0 u hu)) (hv0 u hu)).ne')
  exact integral_mono_on hLW hp hr (fun u hu => logPoly_le b d V t u ht0 (hu0 u hu)
    (hv0 u hu) (hkernel t ht u hu).1 (ha.trans_le hab) (hc.trans_le hcd) hV ht.2
    (hu.2.trans hWd) (hkernel t ht u hu).2)

#print axioms log_four_terms
#print axioms logPoly_le
#print axioms log_inner_continuousOn
#print axioms log_poly_inner_continuous
#print axioms log_integral_compare
end
end LeanLab.Languasco2004.LogRemainder568
