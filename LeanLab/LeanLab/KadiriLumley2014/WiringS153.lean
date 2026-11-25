/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 9 display 2.64 and page 13 Table 2.
Wiring audit, burst-20261122 session S153. The LEAF endpoint_budget_numeric of
SPLIT_table_endpoint_budget_low.lean has the exact twin endpoint_budget_numeric_split, now PROVED
with no sorry, in a file importing that one, so it cannot be closed in place. This file proves
table_endpoint_budget_low_wired, the exact statement of table_endpoint_budget_low_split, through the
twin: CONDITIONAL ON endpoint_low_height_zero_sum and endpoint_high_height_zero_tail alone.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_endpoint_budget_numeric

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

example : type_of% @endpoint_budget_numeric_split = type_of% @endpoint_budget_numeric := rfl

/-- Page 9 display 2.64 at the endpoint of the sixteen low rows of Table 2. CONDITIONAL ON the two
zero sum LEAFs; the numeric step is PROVED. -/
theorem table_endpoint_budget_low_wired {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  have hL0 : 0 ≤ lowZeroBudget r.logIndex := by
    simpa using endpoint_low_height_zero_sum hr hlow ∅
  have hH0 : 0 ≤ highZeroBudget r.logIndex := by
    simpa using endpoint_high_height_zero_tail hr hlow ∅
  have hZ : zeroError r.m r.deltaQ r.uQ (rowEndpointX r) ≤
      lowZeroBudget r.logIndex + highZeroBudget r.logIndex := by
    unfold zeroError
    refine tsum_le_of_sum_le' (by linarith) (fun s => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => |ρ.1.im| ≤ 30610000000)]
    exact add_le_add (endpoint_low_height_zero_sum hr hlow s)
      (endpoint_high_height_zero_tail hr hlow s)
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hth : 0 < r.threshold := by
    unfold PrintedRow.threshold
    split_ifs
    · norm_num [evenBase]
    · exact Real.exp_pos _
  have hX : 0 < rowEndpointX r := by
    unfold rowEndpointX
    have := Real.exp_pos (r.uQ : ℝ)
    positivity
  have hE : 0 < Real.exp (r.uQ : ℝ) - 1 := by
    have := Real.add_one_lt_exp hu.ne'
    linarith
  have hP : 0 < (Real.exp r.uQ - 1) * rowEndpointX r := mul_pos hE hX
  refine (endpoint_budget_numeric_split hr hlow).trans_le ?_
  apply mul_le_mul_of_nonneg_left _ hP.le
  linarith


example : type_of% @table_endpoint_budget_low_wired = type_of% @table_endpoint_budget_low_split := rfl

end LeanLab.KadiriLumley2014.Task92
