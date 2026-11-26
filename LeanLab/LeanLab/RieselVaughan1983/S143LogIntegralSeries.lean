import LeanLab.RieselVaughan1983.S143LogIntegralSub

/-! Split of the HARD leaf `S143LogIntegralSub.integral_log_one_add_div`, Riesel and
Vaughan 1983, Ark. Mat. 21, page 53: the integral of log(1+t)/t from 1/z to 1 as the
difference of the integrals from 0, the termwise series for the integral from 0 to w,
and the alternating Basel value pi^2/12. Each leaf was checked numerically with mpmath
at w = 0.37 before it was stated. The assembly has no sorry of its own.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.S143LogIntegralSeries
open Real MeasureTheory
open LeanLab.RieselVaughan1983.S143SplitLemma3
noncomputable section

/-- Page 53, additivity of the integral of log(1+t)/t over 0 < t ≤ 1, which is
integrable there since the integrand is bounded by 1. PROVED. -/
theorem integral_split_at (z : ℝ) (hz : 1 ≤ z) :
    (∫ t in Set.Ioc (1 / z) 1, log (1 + t) / t) =
      (∫ t in Set.Ioc 0 1, log (1 + t) / t) - (∫ t in Set.Ioc 0 (1 / z), log (1 + t) / t) := by
  have hz0 : 0 < z := by linarith
  have hle : 1 / z ≤ 1 := by rw [div_le_one hz0]; exact hz
  have ha : 0 < 1 / z := by positivity
  have hI : IntegrableOn (fun t : ℝ => log (1 + t) / t) (Set.Ioc 0 1) := by
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne ?_ ?_
    · exact ((measurable_log.comp (measurable_const.add measurable_id)).div
        measurable_id).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
      intro t ht
      have ht0 : 0 < t := ht.1
      have hl0 : 0 ≤ log (1 + t) := log_nonneg (by linarith)
      have hl1 : log (1 + t) ≤ t := by
        have := log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + t); linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hl0 ht0.le), div_le_one ht0]
      exact hl1
  have hab : IntervalIntegrable (fun t : ℝ => log (1 + t) / t) volume 0 (1 / z) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).2
      (hI.mono_set (Set.Ioc_subset_Ioc_right hle))
  have hbc : IntervalIntegrable (fun t : ℝ => log (1 + t) / t) volume (1 / z) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2
      (hI.mono_set (Set.Ioc_subset_Ioc_left ha.le))
  rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le ha.le]
  have := intervalIntegral.integral_add_adjacent_intervals hab hbc
  linarith

/-- LEAF: page 53, the series log(1+t)/t = sum (-1)^h t^h/(h+1) integrated termwise
from 0 to w, for 0 < w ≤ 1. HARD -/
theorem integral_log_one_add_div_series (w : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    (∫ t in Set.Ioc 0 w, log (1 + t) / t) =
      ∑' h : ℕ, (-1 : ℝ) ^ h * w ^ (h + 1) / ((h : ℝ) + 1) ^ 2 := by
  sorry

/-- Page 53, the alternating Basel value sum (-1)^h/(h+1)^2 = pi^2/12, from
zeta 2 = pi^2/6 by splitting even and odd terms. PROVED. -/
theorem alternating_basel :
    (∑' h : ℕ, (-1 : ℝ) ^ h / ((h : ℝ) + 1) ^ 2) = π ^ 2 / 12 := by
  set f : ℕ → ℝ := fun h => 1 / ((h : ℝ) + 1) ^ 2 with hf
  have hS : HasSum f (π ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero] at h
    simpa [hf, Nat.cast_add, Nat.cast_one] using h
  have hfs : Summable f := hS.summable
  have he : Summable fun k => f (2 * k) :=
    hfs.comp_injective (fun a b h => by simpa using h)
  have ho : Summable fun k => f (2 * k + 1) :=
    hfs.comp_injective (fun a b h => by simpa using h)
  have hodd : (fun k => f (2 * k + 1)) = fun k => (1 / 4 : ℝ) * f k := by
    funext k; simp only [hf]; push_cast
    have : (0:ℝ) < (k:ℝ) + 1 := by positivity
    field_simp; ring
  set g : ℕ → ℝ := fun h => (-1 : ℝ) ^ h / ((h : ℝ) + 1) ^ 2 with hg
  have hge : (fun k => g (2 * k)) = fun k => f (2 * k) := by
    funext k; simp only [hg, hf, pow_mul]; norm_num
  have hgo : (fun k => g (2 * k + 1)) = fun k => -(1 / 4 : ℝ) * f k := by
    funext k
    have := congrFun hodd k
    simp only [hg, pow_succ, pow_mul] at this ⊢
    norm_num at this ⊢
    rw [← this]; simp only [hf]; push_cast; ring
  have hgs_e : Summable fun k => g (2 * k) := by rw [hge]; exact he
  have hgs_o : Summable fun k => g (2 * k + 1) := by rw [hgo]; exact hfs.mul_left _
  rw [← tsum_even_add_odd hgs_e hgs_o, hge, hgo, tsum_mul_left]
  have hf2 := tsum_even_add_odd he ho
  rw [hodd, tsum_mul_left, hS.tsum_eq] at hf2
  rw [hS.tsum_eq]
  linarith

/-- Page 53, T z / 2 is the series of the integral from 0 to 1/z. PROVED. -/
theorem T_half_eq (z : ℝ) (hz : 1 ≤ z) :
    T z / 2 = ∑' h : ℕ, (-1 : ℝ) ^ h * (1 / z) ^ (h + 1) / ((h : ℝ) + 1) ^ 2 := by
  have hz0 : 0 < z := by linarith
  unfold T
  rw [← tsum_div_const]
  congr 1
  funext h
  rw [div_pow, one_pow]
  field_simp

/-- Assembly of `integral_log_one_add_div` from the four leaves above. CONDITIONAL ON them. -/
theorem integral_log_one_add_div_of_leaves :
    type_of% @LeanLab.RieselVaughan1983.S143LogIntegralSub.integral_log_one_add_div := by
  intro z hz
  have hz0 : 0 < z := by linarith
  have hle : 1 / z ≤ 1 := by rw [div_le_one hz0]; exact hz
  rw [integral_split_at z hz, integral_log_one_add_div_series 1 one_pos le_rfl,
    integral_log_one_add_div_series (1 / z) (by positivity) hle, ← T_half_eq z hz]
  simp only [one_pow, mul_one]
  rw [alternating_basel]

end
end LeanLab.RieselVaughan1983.S143LogIntegralSeries
#print axioms LeanLab.RieselVaughan1983.S143LogIntegralSeries.T_half_eq
#print axioms LeanLab.RieselVaughan1983.S143LogIntegralSeries.integral_split_at
#print axioms LeanLab.RieselVaughan1983.S143LogIntegralSeries.alternating_basel
