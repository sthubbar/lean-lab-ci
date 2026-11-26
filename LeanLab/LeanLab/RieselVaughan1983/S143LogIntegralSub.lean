import LeanLab.RieselVaughan1983.S143LogIntegral

/-! Split of the HARD leaf `S143LogIntegral.integral_log_div_add`, Riesel and
Vaughan 1983, Ark. Mat. 21, page 53: the substitution u = z t, the elementary
integral of 1/(1+t), integration by parts of log t / (1+t), and the termwise
integral of log(1+t)/t against the alternating Basel value pi^2/12.
Each leaf was checked numerically with mpmath at z = 7.3 before it was stated.
The assembly has no sorry of its own. AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.S143LogIntegralSub
open Real MeasureTheory
open LeanLab.RieselVaughan1983.S143SplitLemma3
noncomputable section

/-- Page 53, the substitution u = z t in the integral of log u / (z+u) over
1 < u ≤ z, with log (z t) = log z + log t. PROVED. -/
theorem subst_zt (z : ℝ) (hz : 1 ≤ z) :
    (∫ u in Set.Ioc 1 z, log u / (z + u)) =
      log z * (∫ t in Set.Ioc (1 / z) 1, 1 / (1 + t)) +
        (∫ t in Set.Ioc (1 / z) 1, log t / (1 + t)) := by
  have hz0 : 0 < z := by linarith
  have hle : 1 / z ≤ 1 := by rw [div_le_one hz0]; exact hz
  rw [← intervalIntegral.integral_of_le hz, ← intervalIntegral.integral_of_le hle,
    ← intervalIntegral.integral_of_le hle]
  have hpos : ∀ t ∈ Set.uIcc (1 / z) 1, 0 < t := by
    intro t ht; rw [Set.uIcc_of_le hle] at ht; have : 0 < 1 / z := by positivity
    linarith [ht.1]
  have key := intervalIntegral.integral_comp_mul_left (fun u => log u / (z + u))
    (a := 1 / z) (b := 1) hz0.ne'
  have hza : z * (1 / z) = 1 := by field_simp
  rw [hza, mul_one, smul_eq_mul] at key
  have hmain : (∫ u in (1:ℝ)..z, log u / (z + u)) = z * ∫ t in (1 / z)..1, log (z * t) / (z + z * t) := by
    rw [key]; field_simp
  rw [hmain]
  have h1 : IntervalIntegrable (fun t => 1 / (1 + t)) volume (1 / z) 1 :=
    (continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun t ht => by have := hpos t ht; dsimp; linarith)).intervalIntegrable
  have h2 : IntervalIntegrable (fun t => log t / (1 + t)) volume (1 / z) 1 :=
    ((continuousOn_log.mono (fun t ht => (hpos t ht).ne')).div
      (continuousOn_const.add continuousOn_id)
      (fun t ht => by have := hpos t ht; dsimp; linarith)).intervalIntegrable
  have hcongr : (∫ t in (1 / z)..1, log (z * t) / (z + z * t)) =
      ∫ t in (1 / z)..1, z⁻¹ * (log z * (1 / (1 + t)) + log t / (1 + t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 := hpos t ht
    have h1t : 0 < 1 + t := by linarith
    dsimp
    rw [log_mul hz0.ne' ht0.ne']
    field_simp
  rw [hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (h1.const_mul _) h2, intervalIntegral.integral_const_mul]
  field_simp

/-- Page 53, the elementary integral of 1/(1+t) from 1/z to 1. PROVED. -/
theorem integral_inv_one_add (z : ℝ) (hz : 1 ≤ z) :
    (∫ t in Set.Ioc (1 / z) 1, 1 / (1 + t)) = log 2 - log (1 + 1 / z) := by
  have hz0 : 0 < z := by linarith
  have hle : 1 / z ≤ 1 := by rw [div_le_one hz0]; exact hz
  have ha : 0 < 1 / z := by positivity
  rw [← intervalIntegral.integral_of_le hle]
  have hpos : ∀ t ∈ Set.uIcc (1 / z) 1, 0 < 1 + t := by
    intro t ht; rw [Set.uIcc_of_le hle] at ht; linarith [ht.1]
  have hd : ∀ t ∈ Set.uIcc (1 / z) 1, HasDerivAt (fun y => log (1 + y)) (1 / (1 + t)) t := by
    intro t ht
    have h := ((hasDerivAt_id t).const_add 1).log (hpos t ht).ne'
    simpa [id] using h
  have hcont : ContinuousOn (fun t => 1 / (1 + t)) (Set.uIcc (1 / z) 1) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun t ht => (hpos t ht).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  norm_num

/-- Page 53, integration by parts of log t / (1+t) from 1/z to 1,
with boundary term log(1/z) log(1+1/z). PROVED. -/
theorem parts_log_div_one_add (z : ℝ) (hz : 1 ≤ z) :
    (∫ t in Set.Ioc (1 / z) 1, log t / (1 + t)) =
      log z * log (1 + 1 / z) - (∫ t in Set.Ioc (1 / z) 1, log (1 + t) / t) := by
  have hz0 : 0 < z := by linarith
  have hle : 1 / z ≤ 1 := by rw [div_le_one hz0]; exact hz
  have ha : 0 < 1 / z := by positivity
  rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
  have hpos : ∀ t ∈ Set.uIcc (1 / z) 1, 0 < t := by
    intro t ht; rw [Set.uIcc_of_le hle] at ht; linarith [ht.1]
  have hu : ∀ t ∈ Set.uIcc (1 / z) 1, HasDerivAt log t⁻¹ t :=
    fun t ht => hasDerivAt_log (hpos t ht).ne'
  have hv : ∀ t ∈ Set.uIcc (1 / z) 1, HasDerivAt (fun y => log (1 + y)) (1 / (1 + t)) t := by
    intro t ht
    have h := ((hasDerivAt_id t).const_add 1).log (by have := hpos t ht; simp only [id]; linarith : (1 + id t) ≠ 0)
    simpa [id] using h
  have hu' : IntervalIntegrable (fun t => t⁻¹) volume (1 / z) 1 :=
    (continuousOn_inv₀.mono (fun t ht => (hpos t ht).ne')).intervalIntegrable
  have hv' : IntervalIntegrable (fun t => 1 / (1 + t)) volume (1 / z) 1 :=
    (continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun t ht => by have := hpos t ht; dsimp; linarith)).intervalIntegrable
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have e1 : (∫ t in (1 / z)..1, log t / (1 + t)) =
      ∫ t in (1 / z)..1, log t * (1 / (1 + t)) := by
    congr 1; funext t; ring
  have e2 : (∫ t in (1 / z)..1, log (1 + t) / t) =
      ∫ t in (1 / z)..1, t⁻¹ * log (1 + t) := by
    congr 1; funext t; ring
  rw [e1, e2, hparts]
  simp only [log_one, zero_mul, one_div, log_inv]
  ring

/-- LEAF: page 53, the series log(1+t)/t = sum (-1)^h t^h/(h+1) integrated termwise
from 1/z to 1, with the alternating Basel value sum (-1)^h/(h+1)^2 = pi^2/12. HARD -/
theorem integral_log_one_add_div (z : ℝ) (hz : 1 ≤ z) :
    (∫ t in Set.Ioc (1 / z) 1, log (1 + t) / t) = π ^ 2 / 12 - T z / 2 := by
  sorry

/-- Assembly of `integral_log_div_add` from the four leaves above. CONDITIONAL ON them. -/
theorem integral_log_div_add_of_leaves :
    type_of% @LeanLab.RieselVaughan1983.S143LogIntegral.integral_log_div_add := by
  intro z hz
  rw [subst_zt z hz, integral_inv_one_add z hz, parts_log_div_one_add z hz,
    integral_log_one_add_div z hz]
  ring

end
end LeanLab.RieselVaughan1983.S143LogIntegralSub
#print axioms LeanLab.RieselVaughan1983.S143LogIntegralSub.integral_inv_one_add
#print axioms LeanLab.RieselVaughan1983.S143LogIntegralSub.parts_log_div_one_add
#print axioms LeanLab.RieselVaughan1983.S143LogIntegralSub.subst_zt
