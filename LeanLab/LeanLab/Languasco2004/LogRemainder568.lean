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
    logPoly T U V t u ≤ (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  obtain ⟨hA0, hA1⟩ := invPoly5_bounds t T ht hT htT
  obtain ⟨hB0, hB1⟩ := invPoly7_bounds u U hu hU huU
  obtain ⟨hv0, hv1⟩ := invPoly3_bounds (1 - t - u) V hv hV hvV
  set v := invPoly3 (1 - t - u) V with hvdef
  set z := (1 - t - 3 * u) * v with hzdef
  have hv0' : 0 ≤ v := by rw [hvdef]; exact hv0
  have hv1' : v ≤ 1 / (1 - t - u) := by rw [hvdef]; exact hv1
  have hz0 : 0 ≤ z := by rw [hzdef]; exact mul_nonneg ha hv0'
  have hvD : v * (1 - t - u) ≤ 1 := (le_div_iff₀ hv).mp hv1'
  have hzD : z * (1 - t - u) ≤ 1 - t - 3 * u := by
    have := mul_le_mul_of_nonneg_left hvD ha
    calc z * (1 - t - u) = (1 - t - 3 * u) * (v * (1 - t - u)) := by
          rw [hzdef]; ring
      _ ≤ (1 - t - 3 * u) * 1 := this
      _ = 1 - t - 3 * u := by ring
  have hzlt : z < 1 := by
    rcases le_or_gt 1 z with hge | hlt
    · have h2 : (1 : ℝ) * (1 - t - u) ≤ z * (1 - t - u) :=
        mul_le_mul_of_nonneg_right hge hv.le
      nlinarith [hzD, h2]
    · exact hlt
  have hlog4 := log_four_terms z hz0 hzlt
  have hz1pos : 0 < 1 - z := by linarith
  have hexp : (1 - t) / u - 2 = (1 - t - 2 * u) / u := by field_simp
  have hratio : (1 + z) / (1 - z) ≤ (1 - t) / u - 2 := by
    rw [div_le_iff₀ hz1pos, hexp]
    have hkey : u * (1 + z) ≤ (1 - t - 2 * u) * (1 - z) := by nlinarith [hzD]
    rw [div_mul_eq_mul_div₀, le_div_iff₀ hu]
    linarith [hkey]
  have hposA : 0 < (1 + z) / (1 - z) := div_pos (by linarith) hz1pos
  have hposB : 0 < (1 - t) / u - 2 := by
    have h : 0 < (1 - t - 2 * u) / u := div_pos (by linarith) hu
    rwa [← hexp] at h
  have hlog : 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7 ≤ Real.log ((1 - t) / u - 2) :=
    le_trans hlog4 (Real.log_le_log hposA hratio)
  have hPz0 : 0 ≤ 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7 := by
    nlinarith [hz0, pow_nonneg hz0 3, pow_nonneg hz0 5, pow_nonneg hz0 7]
  have hAt : invPoly5 t T * t ≤ 1 := (le_div_iff₀ ht).mp hA1
  have hBu : invPoly7 u U * u ≤ 1 := (le_div_iff₀ hu).mp hB1
  have hAt0 : 0 ≤ invPoly5 t T * t := mul_nonneg hA0 ht.le
  have hBu0 : 0 ≤ invPoly7 u U * u := mul_nonneg hB0 hu.le
  have hvD0 : 0 ≤ v * (1 - t - u) := mul_nonneg hv0' hv.le
  have hprod : invPoly5 t T * invPoly7 u U * v * (t * u * (1 - t - u)) ≤ 1 := by
    have hp1 : (invPoly5 t T * t) * (invPoly7 u U * u) ≤ 1 := by
      have h := mul_le_mul hAt hBu hBu0 (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h
    have hp2 : ((invPoly5 t T * t) * (invPoly7 u U * u)) * (v * (1 - t - u)) ≤ 1 := by
      have h := mul_le_mul hp1 hvD hvD0 (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h
    calc invPoly5 t T * invPoly7 u U * v * (t * u * (1 - t - u))
        = ((invPoly5 t T * t) * (invPoly7 u U * u)) * (v * (1 - t - u)) := by ring
      _ ≤ 1 := hp2
  have hLHS : logPoly T U V t u
      = invPoly5 t T * invPoly7 u U * v *
        (1 + 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7) := by
    simp only [logPoly]
    rw [← hvdef, ← hzdef]
  have hD : 0 < t * u * (1 - t - u) := mul_pos (mul_pos ht hu) hv
  have h1P : 0 ≤ 1 + 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7 := by linarith
  have hstep : logPoly T U V t u ≤
      (1 + 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7) / (t * u * (1 - t - u)) := by
    rw [hLHS, le_div_iff₀ hD]
    calc invPoly5 t T * invPoly7 u U * v *
          (1 + 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7) * (t * u * (1 - t - u))
        = (invPoly5 t T * invPoly7 u U * v * (t * u * (1 - t - u))) *
          (1 + 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7) := by ring
      _ ≤ 1 * (1 + 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7) :=
          mul_le_mul_of_nonneg_right hprod h1P
      _ = 1 + 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7 := by ring
  calc logPoly T U V t u
      ≤ (1 + 2 * z + 2 / 3 * z^3 + 2 / 5 * z^5 + 2 / 7 * z^7) / (t * u * (1 - t - u)) := hstep
    _ ≤ (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
        exact (div_le_div_iff₀ hD hD).mpr
          (mul_le_mul_of_nonneg_right (by linarith) hD.le)

/-- LEAF. Pages 279 and 280: continuity of the logarithmic inner integral on a positive rectangle. -/
theorem log_inner_continuousOn (a b c d : ℝ) (L U : ℝ → ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hbd : b + 2 * d < 1)
    (hL : Continuous L) (hU : Continuous U)
    (hbound : ∀ t ∈ Icc a b, c ≤ L t ∧ L t ≤ U t ∧ U t ≤ d) :
    ContinuousOn (fun t : ℝ => ∫ u in L t..U t,
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u))) (Icc a b) := by
  have hrect : ∀ p ∈ Icc a b ×ˢ Icc c d,
      0 < p.1 ∧ 0 < p.2 ∧ 0 < 1 - p.1 - p.2 ∧ 0 < (1 - p.1) / p.2 - 2 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hpa, hpb⟩ := hp1
    obtain ⟨hpc, hpd⟩ := hp2
    have hp1pos : 0 < p.1 := lt_of_lt_of_le ha hpa
    have hp2pos : 0 < p.2 := lt_of_lt_of_le hc hpc
    have hsum : p.1 + 2 * p.2 < 1 := by linarith
    refine ⟨hp1pos, hp2pos, by linarith, ?_⟩
    have hgt : 2 < (1 - p.1) / p.2 := (lt_div_iff₀ hp2pos).mpr (by linarith)
    linarith
  have hF : ContinuousOn (Function.uncurry
      (fun t u : ℝ => (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u))))
      (Icc a b ×ˢ Icc c d) := by
    have hnum : ContinuousOn (fun p : ℝ × ℝ => (1 - p.1) / p.2 - 2)
        (Icc a b ×ˢ Icc c d) :=
      (((continuousOn_const.sub continuousOn_fst).div continuousOn_snd
        (fun p hp => (hrect p hp).2.1.ne')).sub continuousOn_const)
    have hlog : ContinuousOn (fun p : ℝ × ℝ => Real.log ((1 - p.1) / p.2 - 2))
        (Icc a b ×ˢ Icc c d) :=
      hnum.log (fun p hp => (hrect p hp).2.2.2.ne')
    have hden : ContinuousOn (fun p : ℝ × ℝ => p.1 * p.2 * (1 - p.1 - p.2))
        (Icc a b ×ˢ Icc c d) := by fun_prop
    have hne : ∀ p ∈ Icc a b ×ˢ Icc c d, p.1 * p.2 * (1 - p.1 - p.2) ≠ 0 := by
      intro p hp
      obtain ⟨hp1, hp2, hp3, _⟩ := hrect p hp
      exact (mul_pos (mul_pos hp1 hp2) hp3).ne'
    exact (continuousOn_const.add hlog).div hden hne
  exact moving_integral_continuousOn
    (fun t u : ℝ => (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)))
    a b c d L U hab hcd hF hL hU (by
      intro t ht
      obtain ⟨h1, h2, h3⟩ := hbound t ht
      exact ⟨h1, h2.trans h3, h1.trans h2, h3⟩)

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
