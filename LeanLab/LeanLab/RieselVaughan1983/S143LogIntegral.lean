import LeanLab.RieselVaughan1983.S143SplitLemma3

/-! Split of the leaf `S143SplitLemma3.log_integral_series`, Riesel and Vaughan
1983, Ark. Mat. 21, page 53. The integrand 2 z log u / (u (z+u)) is split by the
partial fraction z / (u (z+u)) = 1/u - 1/(z+u); the first piece is the elementary
integral of log u / u, the second is the dilogarithm type integral giving
log 2 log z - pi^2/12 + T z / 2. Each leaf was checked numerically with mpmath
at z = 7.3 before it was stated. The assembly has no sorry of its own.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.S143LogIntegral
open Real MeasureTheory
open LeanLab.RieselVaughan1983.S143SplitLemma3
noncomputable section

/-- Page 53, partial fraction z / (u (z+u)) = 1/u - 1/(z+u) under the integral,
with integrability of both pieces on 1 < u ≤ z. PROVED. -/
theorem partial_fraction_split (z : ℝ) (hz : 1 ≤ z) :
    (∫ u in Set.Ioc 1 z, 2 * z * log u / (u * (z + u))) =
      2 * (∫ u in Set.Ioc 1 z, log u / u) - 2 * (∫ u in Set.Ioc 1 z, log u / (z + u)) := by
  simp only [← intervalIntegral.integral_of_le hz]
  have hpos : ∀ u ∈ Set.uIcc 1 z, 0 < u := by
    intro u hu; rw [Set.uIcc_of_le hz] at hu; linarith [hu.1]
  have hlog : ContinuousOn log (Set.uIcc 1 z) :=
    continuousOn_log.mono (fun u hu => (hpos u hu).ne')
  have h1 : IntervalIntegrable (fun u => log u / u) volume 1 z :=
    (hlog.div continuousOn_id (fun u hu => (hpos u hu).ne')).intervalIntegrable
  have h2 : IntervalIntegrable (fun u => log u / (z + u)) volume 1 z :=
    (hlog.div (continuousOn_const.add continuousOn_id)
      (fun u hu => by have := hpos u hu; dsimp; linarith)).intervalIntegrable
  have hcongr : (∫ u in (1:ℝ)..z, 2 * z * log u / (u * (z + u))) =
      ∫ u in (1:ℝ)..z, (2 * (log u / u) - 2 * (log u / (z + u))) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 := hpos u hu
    have hzu : 0 < z + u := by linarith
    dsimp
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_sub (h1.const_mul 2) (h2.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- Page 53, the elementary integral of log u / u from 1 to z is (log z)^2 / 2. PROVED. -/
theorem integral_log_div_self (z : ℝ) (hz : 1 ≤ z) :
    (∫ u in Set.Ioc 1 z, log u / u) = log z ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hz]
  have hpos : ∀ u ∈ Set.uIcc 1 z, 0 < u := by
    intro u hu; rw [Set.uIcc_of_le hz] at hu; linarith [hu.1]
  have hd : ∀ u ∈ Set.uIcc 1 z, HasDerivAt (fun y => log y ^ 2 / 2) (log u / u) u := by
    intro u hu
    have h := ((hasDerivAt_log (hpos u hu).ne').pow 2).div_const 2
    convert h using 1
    field_simp
    norm_num
    ring
  have hcont : ContinuousOn (fun u => log u / u) (Set.uIcc 1 z) := by
    apply ContinuousOn.div
    · exact continuousOn_log.mono (fun u hu => (hpos u hu).ne')
    · exact continuousOn_id
    · exact fun u hu => (hpos u hu).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)]
  simp

/-- LEAF: page 53, after u = z t and the termwise integration of log(1+t)/t with the
alternating Basel value pi^2/12, the integral of log u / (z+u) from 1 to z equals
log 2 log z - pi^2/12 + T z / 2. HARD -/
theorem integral_log_div_add (z : ℝ) (hz : 1 ≤ z) :
    (∫ u in Set.Ioc 1 z, log u / (z + u)) = log 2 * log z - π ^ 2 / 12 + T z / 2 := by
  have hz0 : 0 < z := by linarith
  rw [← intervalIntegral.integral_of_le hz]
  sorry

/-- Assembly of `log_integral_series` from the three leaves above. CONDITIONAL ON them. -/
theorem log_integral_series_of_leaves :
    type_of% @LeanLab.RieselVaughan1983.S143SplitLemma3.log_integral_series := by
  intro z hz
  rw [partial_fraction_split z hz, integral_log_div_self z hz, integral_log_div_add z hz]
  ring

end
end LeanLab.RieselVaughan1983.S143LogIntegral

#print axioms LeanLab.RieselVaughan1983.S143LogIntegral.integral_log_div_self
#print axioms LeanLab.RieselVaughan1983.S143LogIntegral.partial_fraction_split
