/-
P0006, page 2, the logarithmic number of multiplications in step 6.
The operation count is powerMulCount in PowerCost98.lean, which follows Pratt.pm.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.PowerCost98

open scoped Asymptotics

namespace LeanLab.HelfgottPlatt.Task98

/-- Page 2, an explicit bound implying the stated Big O estimate.
The constant 4 / log 2 is derived here and is not a printed paper constant. -/
theorem powerCost_le_log {N : ℕ} (hN : 2 ≤ N) :
    (powerMulCount (N.log2 + 1) ((N - 1) / 2) : ℝ) ≤
      (4 / Real.log 2) * Real.log N := by
  have hpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : (N.log2 : ℝ) ≤ Real.log N / Real.log 2 := by
    simpa [Real.logb] using Real.log2_le_logb N
  have hprod : (N.log2 : ℝ) * Real.log 2 ≤ Real.log N :=
    (le_div_iff₀ hpos).mp hlog
  have hlogN : Real.log (2 : ℝ) ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hc : (powerMulCount (N.log2 + 1) ((N - 1) / 2) : ℝ) ≤
      2 * ((N.log2 : ℝ) + 1) := by
    exact_mod_cast powerMulCount_le (N.log2 + 1) ((N - 1) / 2)
  have hc' := mul_le_mul_of_nonneg_right hc hpos.le
  calc
    _ ≤ 4 * Real.log N / Real.log 2 := (le_div_iff₀ hpos).mpr (by nlinarith)
    _ = (4 / Real.log 2) * Real.log N := by ring

/-- Page 2, the sentence after step 6. The number of ring multiplications
for the modular half exponent is O of log N as N tends to infinity. -/
theorem powerCost_isBigO :
    (fun N : ℕ => (powerMulCount (N.log2 + 1) ((N - 1) / 2) : ℝ))
      =O[Filter.atTop] (fun N : ℕ => Real.log N) := by
  apply Asymptotics.IsBigO.of_bound (4 / Real.log 2)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hc : (0 : ℝ) ≤ (powerMulCount (N.log2 + 1) ((N - 1) / 2) : ℝ) :=
    Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hlog]
    using powerCost_le_log hN

end LeanLab.HelfgottPlatt.Task98
