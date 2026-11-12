/-
P0059 arXiv 1407.7902v1 page 7 Lemma 2.5, pages 8 and 9 Lemma 2.6 and equation 2.64,
page 11 Theorem 3.2 and page 13 Table 2.
The zero term zeroError of the endpoint leaf Task92.table_endpoint_budget is bounded in the
paper by the positive six-term envelope of Lemma 2.6, fed by the Theorem 3.2 inputs.
This file proves the reduction of the endpoint leaf to that envelope, CONDITIONAL ON
Task259.lemma2_6_positive and the five cited ZeroInputs259 leaves, with the numerical
envelope inequality kept as an explicit hypothesis. It does NOT state that numerical
inequality as a leaf: an uncertified mpmath probe finds it false on all twenty rows,
see research/burst-20261112/KadiriLumley2014-table_endpoint_budget.md.
AI wrote this Lean code, burst3 2026-11-12. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.Decomp92
import LeanLab.KadiriLumley2014.ZeroBudget259

namespace LeanLab.KadiriLumley2014.Task92

open Real Set MeasureTheory
open Task64 Task259 Task301

/-- Page 9 equation 2.64 with the zero sum bounded as in Lemma 2.6, at the row endpoint
rowEndpointX r and the cut aQ + 1/10000 of table_endpoint_budget.
If the paper's envelope budget, built from Lemma 2.5, Lemma 2.6 and Theorem 3.2 with a
height T1 and a sigma row of Table 1, is below 1 + delta/2, then the endpoint budget holds.
CONDITIONAL ON lemma2_6_positive, OPEN, and the five cited Theorem 3.2 inputs.
AI wrote this Lean code, burst3 2026-11-12. -/
theorem table_endpoint_budget_of_envelope {r : PrintedRow} (hr : r ∈ tableTwo)
    {T1 : ℝ} {d : ℕ × ℚ × ℚ × ℚ} (hd : d ∈ densityTable)
    (hT0 : 1132491 ≤ T1) (hTH : T1 ≤ 30610000000)
    (hlog : Real.log (rowEndpointX r) < 5.69693 * r.m * (Real.log 30610000000) ^ 2)
    (hnum : envelopeBudget r.m r.deltaQ r.uQ (rowEndpointX r) ((r.aQ : ℝ) + 1 / 10000) T1
      ((d.1 : ℝ) / 100) d.2.1 d.2.2.1 d.2.2.2 < 1 + (r.deltaQ : ℝ) / 2) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  have hp := tableTwo_parameters r hr
  have hs := table_small_steps r hr
  have hm : 2 ≤ r.m := hp.1
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hδ1 : (r.deltaQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    norm_num at h ⊢
    exact h
  have hu : (0 : ℝ) < r.uQ := by
    have h : (1 / (10 : ℝ) ^ 12) ≤ r.uQ := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
      norm_num at hh ⊢
      exact hh
    linarith
  have hu1 : (r.uQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    norm_num at h ⊢
    exact h
  have hm0 : (r.m : ℝ) ≠ 0 := by exact_mod_cast (show r.m ≠ 0 by omega)
  have hδu : (r.deltaQ : ℝ) = r.m * (r.uQ : ℝ) := by
    simp only [PrintedRow.uQ, Rat.cast_div, Rat.cast_natCast]
    field_simp
  have hdpar := densityTable_domain d hd
  have hc1 : (0 : ℝ) ≤ d.2.1 := by exact_mod_cast hdpar.2.2.1.le
  have hc2 : (0 : ℝ) ≤ d.2.2.1 := by exact_mod_cast hdpar.2.2.2.1.le
  have hσ : (3 / 5 : ℝ) < (d.1 : ℝ) / 100 := by
    have h : (60 : ℝ) < d.1 := by exact_mod_cast hdpar.1
    linarith
  have hσ1 : (d.1 : ℝ) / 100 < 1 := by
    have h : (d.1 : ℝ) < 100 := by exact_mod_cast hdpar.2.1
    linarith
  -- the endpoint is admissible, from the earlier domain lemma at X = rowEndpointX r
  have hrpar := (tableTwo_rounding_arithmetic r hr).1
  have haQ : (0 : ℝ) ≤ r.aQ := by exact_mod_cast hrpar.2.2.2.1
  have hY38 : Real.exp 38 ≤ rowEndpointX r := by
    have hS : 0 < Real.exp r.uQ * (1 + (r.deltaQ : ℝ)) := by positivity
    have he : Real.exp (r.uQ : ℝ) ≤ 2 := by
      have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.0001)
        (by norm_num : (0.0001 : ℝ) < 1)
      have hu' := Real.exp_le_exp.mpr hu1
      norm_num at h
      linarith
    have hS4 : Real.exp r.uQ * (1 + (r.deltaQ : ℝ)) ≤ 4 := by
      nlinarith [Real.exp_pos (r.uQ : ℝ)]
    have hbase : (4 * 10 ^ 18 : ℝ) ≤ r.threshold := by
      have h := tableTwo_threshold_ge_base hr
      norm_num [evenBase] at h ⊢
      exact h
    have hlow : (10 : ℝ) ^ 18 ≤ rowEndpointX r := by
      unfold rowEndpointX
      rw [le_div_iff₀ hS]
      nlinarith
    exact exp38_lt_base_quarter.le.trans hlow
  have hY10 : 10 < rowEndpointX r := by linarith [Real.add_one_le_exp (38 : ℝ)]
  have hY0 : 0 < rowEndpointX r := by linarith
  have hS := lemma2_5_positive r.m hm hY10 hT0 hTH hσ hσ1
    published_verified_height published_low_zero_data published_zero_free_region
    published_zero_count (published_zero_density hd) hc1 hc2 hlog
  have hzero := lemma2_6_positive hm hδ hδ1 hu hu1 hδu hY10 hT0 hTH hσ hσ1
    published_verified_height published_low_zero_data published_zero_free_region
    published_zero_count (published_zero_density hd) hc1 hc2 hlog hS
  have hbudget : normalizedBudget r.m r.deltaQ r.uQ (rowEndpointX r)
      ((r.aQ : ℝ) + 1 / 10000) < 1 + (r.deltaQ : ℝ) / 2 := by
    unfold normalizedBudget envelopeBudget at *
    linarith
  exact (normalizedBudget_lt_iff r.m r.deltaQ ((r.aQ : ℝ) + 1 / 10000) hu hY0).mp hbudget

end LeanLab.KadiriLumley2014.Task92
