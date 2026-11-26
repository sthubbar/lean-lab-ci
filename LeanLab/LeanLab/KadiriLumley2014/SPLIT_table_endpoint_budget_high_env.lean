/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, pages 8 and 9 Lemma 2.6 displays 2.50 to 2.58,
page 9 Theorem 2.7 display 2.64 and Table 2 on page 13. Second SPLIT of table_endpoint_budget_high
from SPLIT_table_endpoint_budget.lean, ROUTE BURST S10 burst-20261124, step tablehighd.
The split of step tablehigh bounds the zeros up to H = 3.061e10 by their actual sum, about 0.0097
on row 58, which needs the zeros themselves. This file uses instead the paper's own envelope for
that range, Sigma0 + Sigma1 + Sigma2 of Lemma 2.6 bounded by (B0 + B1 + B2) X^(-1/2) with B0, B1
and B2 of displays 2.51, 2.54 and 2.58, which needs only the inputs of Theorem 2.4 and display
2.28. With the zeros above H handled as in steps tablehighb and tablehighc, through the
verified height 3e12 of Platt and Trudgian 2021, the paper envelope closes all four rows.
Uncertified mpmath at the row endpoint, point iii of the 2026-11-15 falsifier, in units of the
factor (e^u - 1) X: envelope 0.0352884, 0.0214084, 0.0129878, 3.8e-22 on rows 58, 59, 60, 150;
budget before the zero sum 0.0639936, 0.0479281, 0.0414753, 0.0180448; remaining margins after
the rounded budgets 0.02867, 0.02649, 0.02846, 0.01800.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_endpoint_mid_height_zero_sum_high

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- Per row budget for the Lemma 2.6 envelope (B0 + B1 + B2) X^(-1/2) of the zeros of ordinate
at most H = 3.061e10, rows 58, 59, 60 and 150 of Table 2 on page 13; data only, from the
uncertified falsifier values envelope_low at point iii in
notes/burst-20261115/scripts/actualzeros_rows/row_16.json to row_19.json. -/
noncomputable def highRowEnvelopeBudgetS10 : ℕ → ℝ
  | 58 => 0.03530 | 59 => 0.02142 | 60 => 0.01300 | 150 => 0.00002
  | _ => 0

/-- LEAF: pages 8 and 9 Lemma 2.6, displays 2.50 to 2.58, for rows 58, 59, 60 and 150 of Table 2
on page 13: the zeros with ordinate at most H = 3.061e10 contribute at most
(B0 + B1 + B2) X^(-1/2), with B0 = S02 of display 2.51 from N0 = 2001052, B1 = S12 of display
2.54 with the Rosser upper count at T1, and B2 of display 2.58 from S2 of display 2.41, using
Theorem 2.4 a, b and c with H = 3.061e10 and the bounds 2.25 and 2.28. Uncertified mpmath
envelope 0.0352884, 0.0214084, 0.0129878 and 3.8e-22. Class HARD. -/
theorem endpoint_low_height_envelope_high_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => |ρ.1.im| ≤ 30610000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ highRowEnvelopeBudgetS10 r.logIndex := by
  sorry

/-- LEAF: page 9 display 2.64 at the row endpoint with the zero sum replaced by the envelope
budget and the two budgets 1e-5 of the ranges above H, a finite numeric check over rows 58, 59,
60 and 150 of Table 2 on page 13. Uncertified margins 0.02867, 0.02649, 0.02846 and 0.01800 in
units of (e^u - 1) X. Class MEDIUM. -/
theorem endpoint_budget_numeric_env_high_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (highRowEnvelopeBudgetS10 r.logIndex + 1 / 100000 + 1 / 100000)) := by
  sorry

/-- Assembly: the exact statement of table_endpoint_budget_high from the envelope leaf, the
numeric leaf, and the split assemblies of steps tablehighb and tablehighc for the zeros above H. -/
theorem table_endpoint_budget_high_env_split_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  have hL0 : 0 ≤ highRowEnvelopeBudgetS10 r.logIndex := by
    simpa using endpoint_low_height_envelope_high_S10 hr hhigh ∅
  have hZ : zeroError r.m r.deltaQ r.uQ (rowEndpointX r) ≤
      highRowEnvelopeBudgetS10 r.logIndex + 1 / 100000 + 1 / 100000 := by
    unfold zeroError
    refine tsum_le_of_sum_le' (by linarith) (fun s => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => |ρ.1.im| ≤ 30610000000)]
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000))
      (fun ρ => |ρ.1.im| ≤ 3000000000000)]
    rw [Finset.filter_filter]
    have h1 := endpoint_low_height_envelope_high_S10 hr hhigh s
    have h2 := endpoint_mid_height_zero_sum_high_split_S10 hr hhigh s
    have h3 := endpoint_top_height_zero_tail_high_split_S10 hr hhigh
      (s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000))
    linarith
  have hs := table_small_steps r hr
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hX : 0 < rowEndpointX r := by
    unfold rowEndpointX
    have := Real.exp_pos (r.uQ : ℝ)
    have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
    have hth : 0 < r.threshold := by
      unfold PrintedRow.threshold
      split_ifs
      · norm_num [evenBase]
      · exact Real.exp_pos _
    positivity
  have hE : 0 < Real.exp (r.uQ : ℝ) - 1 := by
    have := Real.add_one_lt_exp hu.ne'
    linarith
  have hP : 0 < (Real.exp r.uQ - 1) * rowEndpointX r := mul_pos hE hX
  refine (endpoint_budget_numeric_env_high_S10 hr hhigh).trans_le ?_
  apply mul_le_mul_of_nonneg_left _ hP.le
  linarith

#print axioms table_endpoint_budget_high_env_split_S10

end LeanLab.KadiriLumley2014.Task92
