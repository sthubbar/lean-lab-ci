/-
Jia 1996 page 279, Lemma 26 numerical support.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Kernel568
import LeanLab.Languasco2004.MovingIntegral548
namespace LeanLab.Languasco2004.Numeric568
open Real Set intervalIntegral Kernel568 Numeric30_548 MovingIntegral548 BuchstabInitial316
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- LEAF. Page 279: exact polynomial integration supplies a reserve above the printed coefficient. -/
theorem polynomial4_integral :
    (0.0096365 : ℝ) ≤ ∫ t in (41 / 180 : ℝ)..(8 / 33),
      ∫ u in (41 / 90 - t)..t, polynomial4 t u := by sorry

/-- Page 279: the source logarithmic inner integral. -/
def inner4 (t : ℝ) : ℝ :=
  ∫ u in (41 / 90 - t)..(t),
    (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u))

/-- Page 279: the logarithmic inner integral is continuous on its source t interval. -/
theorem inner4_continuousOn : ContinuousOn inner4 (Icc (41 / 180) (8 / 33)) := by
  let R := Icc (41 / 180 : ℝ) (8 / 33) ×ˢ
    Icc (41 / 90 - (8 / 33 : ℝ)) (8 / 33)
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
    (41 / 180) (8 / 33) (41 / 90 - (8 / 33)) (8 / 33)
    (fun t => 41 / 90 - t) (fun t => t)
    (by norm_num) (by norm_num) hc (by fun_prop) (by fun_prop)
  intro t ht
  have := ht.1
  have := ht.2
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- LEAF. Page 279: the polynomial inner integral is continuous for every real t. -/
theorem polynomial_inner_continuous : Continuous (fun t : ℝ =>
    ∫ u in (41 / 90 - t)..(t), polynomial4 t u) := by sorry

/-- Page 279: the complete logarithmic integral has a reserve above 0.009636. -/
theorem region4_numeric_margin :
    (0.0096365 : ℝ) ≤ ∫ t in (41 / 180 : ℝ)..(8 / 33), inner4 t := by
  have hinner (t : ℝ) (ht : t ∈ Icc (41 / 180 : ℝ) (8 / 33)) :
      (∫ u in (41 / 90 - t)..(t), polynomial4 t u) ≤ inner4 t := by
    have hab : 41 / 90 - t ≤ t := by linarith [ht.1]
    have hp : IntervalIntegrable (polynomial4 t) MeasureTheory.volume
        (41 / 90 - t) (t) := by
      apply Continuous.intervalIntegrable
      unfold polynomial4 Numeric30_548.invPoly3
      fun_prop
    have hr : IntervalIntegrable
        (fun u : ℝ => (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)))
        MeasureTheory.volume (41 / 90 - t) (t) := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      have hu (u : ℝ) (hu : u ∈ Icc (41 / 90 - t) (t)) : 0 < u := by
        linarith [ht.2, hu.1]
      have hv (u : ℝ) (hu : u ∈ Icc (41 / 90 - t) (t)) : 0 < 1 - t - u := by
        linarith [ht.2, hu.2]
      have harg (u : ℝ) (hu : u ∈ Icc (41 / 90 - t) (t)) :
          (1 - t) / u - 2 ≠ 0 := by
        have hpos : 0 < (1 - t) / u - 2 := by
          apply sub_pos.mpr
          apply (lt_div_iff₀ (by linarith [ht.2, hu.1] : 0 < u)).mpr
          linarith [ht.2, hu.2]
        exact hpos.ne'
      have hc : ContinuousOn (fun u : ℝ => (1 - t) / u - 2)
          (Icc (41 / 90 - t) (t)) :=
        ((continuousOn_const.sub continuousOn_const).div continuousOn_id
        (fun u h => (hu u h).ne')).sub continuousOn_const
      exact (continuousOn_const.add (hc.log harg)).div
        (by fun_prop) (fun u h => (mul_pos (mul_pos (by linarith [ht.1]) (hu u h)) (hv u h)).ne')
    exact integral_mono_on hab hp hr
      (fun u hu => polynomial4_le t u ht.1 ht.2 hu.1 hu.2)
  have hm := integral_mono_on (by norm_num : (41 / 180 : ℝ) ≤ 8 / 33)
    (polynomial_inner_continuous.intervalIntegrable _ _)
    (inner4_continuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num)) hinner
  exact polynomial4_integral.trans hm

/-- Page 279: the complete first Buchstab integral is at least 0.009636. -/
theorem region4_buchstab_lower :
    (0.009636 : ℝ) ≤ ∫ t in (41 / 180 : ℝ)..(8 / 33),
      ∫ u in (41 / 90 - t)..(t),
        buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) := by
  have he : (∫ t in (41 / 180 : ℝ)..(8 / 33),
      ∫ u in (41 / 90 - t)..(t),
        buchstabInitial ((1 - t - u) / u) / (t * u ^ 2)) =
      ∫ t in (41 / 180 : ℝ)..(8 / 33), inner4 t := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    apply integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith [ht.1] :
      41 / 90 - t ≤ t)] at hu
    exact Kernel568.region4_kernel t u ht.1 ht.2 hu.1 hu.2
  rw [he]
  linarith [region4_numeric_margin]

#print axioms polynomial4_integral
#print axioms inner4_continuousOn
#print axioms polynomial_inner_continuous
#print axioms region4_numeric_margin
#print axioms region4_buchstab_lower
end
end LeanLab.Languasco2004.Numeric568
