/-
Jia 1996 page 252, Lemma 16 regions i and ii.
Source https://doi.org/10.4064/aa-77-3-207-287.
Check the scope of the region i input used by the false branch task.
These statements concern input coverage only. No analytic transfer is proved.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Languasco2004.InputCoverage583
open Real Filter

/-- Page 252 Lemma 16: these power scales lie strictly inside region ii,
while their P scale exceeds the region i upper endpoint.
This is evidence about the scope of Decomp578a.lemma16_progression_input.
It is not a counterexample to either source region or to a transfer theorem. -/
theorem region_ii_scales (Y : ℝ) (hY : 1 < Y) :
    Y ^ (16 / 135 : ℝ) < Y ^ (7 / 50 : ℝ) ∧
    Y ^ (7 / 50 : ℝ) < Y ^ (3 / 20 : ℝ) ∧
    Y ^ (89 / 462 : ℝ) < Y ^ (1 / 4 : ℝ) ∧
    Y ^ (1 / 4 : ℝ) < Y ^ (17 / 54 : ℝ) ∧
    Y ^ (16 / 135 : ℝ) < Y ^ (3 / 20 : ℝ) ∧
    Y ^ (3 / 20 : ℝ) <
      (Y ^ (1 / 4 : ℝ)) ^ (-29 / 48 : ℝ) * Y ^ (89 / 288 : ℝ) := by
  have hY0 : 0 < Y := lt_trans zero_lt_one hY
  have hupper : (Y ^ (1 / 4 : ℝ)) ^ (-29 / 48 : ℝ) * Y ^ (89 / 288 : ℝ) =
      Y ^ (91 / 576 : ℝ) := by
    rw [← Real.rpow_mul hY0.le, ← Real.rpow_add hY0]
    norm_num
  rw [hupper]
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num),
    Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num),
    Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num),
    Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num),
    Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num),
    Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num)⟩

/-- Page 252 Lemma 16 support: no fixed implicit constant brings these
region ii P scales below the region i cap as Y tends to infinity.
The exponent gap is exactly 53/924. -/
theorem region_i_cap_ratio_tendsto :
    Tendsto (fun Y : ℝ => Y ^ (1 / 4 : ℝ) / Y ^ (89 / 462 : ℝ)) atTop atTop := by
  have h := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 53 / 924)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  rw [← Real.rpow_sub hY]
  norm_num

/-- Page 208 support: the localization Y has exponent 7/12 plus epsilon.
Every logarithmic power is smaller than the power gap between N and Y.
This records why a prefix error allowance on the scale N cannot be absorbed into
the localized error merely by choosing a larger fixed logarithmic saving. -/
theorem logarithmic_saving_below_localization_gap (ε K : ℝ) (hε : ε < 5 / 12) :
    Asymptotics.IsLittleO atTop (fun N : ℝ => log N ^ K)
      (fun N : ℝ => N ^ (5 / 12 - ε)) := by
  exact isLittleO_log_rpow_rpow_atTop K (by linarith)

#print axioms region_ii_scales
#print axioms region_i_cap_ratio_tendsto
#print axioms logarithmic_saving_below_localization_gap
end LeanLab.Languasco2004.InputCoverage583
