/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 4 display 2.20, page 5 display 2.28,
page 6 Theorem 2.4, pages 8 and 9 displays 2.47, 2.59 and 2.60, page 9 Theorem 2.7 and page 13
Table 2. SPLIT of table_endpoint_budget_high from SPLIT_table_endpoint_budget.lean,
ROUTE BURST S10 burst-20261124, step tablehigh.

Theorem 2.4 a of the paper is stated for any verified height H. The paper takes Platt's
H = 3.061e10; at that H the corrected tail does not close rows 58, 59, 60 and 150. Here the
verified height of Platt and Trudgian 2021, H2 = 3e12, is used as a second instance of
Theorem 2.4 a. The zero sum zeroError is cut at both heights:
  zeros with absolute ordinate at most 3.061e10, on the line by Platt 2011, summed as in the
  sibling leaf endpoint_low_height_zero_sum;
  zeros with absolute ordinate in the interval from 3.061e10 to 3e12, on the line by Platt and
  Trudgian, bounded by display 2.28 at real part one half and the count of display 2.47;
  zeros above 3e12, bounded by display 2.59 with sigma0 = 1, that is display 2.28 and 2.47
  at H2 with the trivial factor X^(beta - 1) at most 1, with no zero density input.
Uncertified mpmath values at the row endpoint, point iii of the 2026-11-15 falsifier, in units
of the factor (e^u - 1) X of the right side:
  row, budget before zero sum, zeros to 3.061e10, zeros 3.061e10 to 3e12 bound, above 3e12 bound
  58  0.0639936  0.00968638  1.5e-14  2.4e-123
  59  0.0479281  0.00587643  8.9e-15  2.4e-123
  60  0.0414753  0.00356505  5.5e-15  2.4e-123
  150 0.0180448  1.0e-22     2.3e-34  3.8e-129
The budgets below round each value up at the fifth decimal and add 1e-5, and the two upper
ranges get 1e-5 each. Remaining margins 0.05427, 0.04201, 0.03787, 0.01801.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_table_endpoint_budget

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- Per row budget for the zeros of ordinate at most H = 3.061e10 on the four rows 58, 59, 60
and 150 of Table 2 on page 13, display 2.20 route; data only, from the uncertified falsifier
values notes/burst-20261115/scripts/actualzeros_rows/row_16.json to row_19.json. -/
noncomputable def highRowLowZeroBudgetS10 : ℕ → ℝ
  | 58 => 0.00970 | 59 => 0.00589 | 60 => 0.00358 | 150 => 0.00002
  | _ => 0

/-- LEAF: page 4 display 2.20 for rows 58, 59, 60 and 150 of Table 2 on page 13, the zeros with
ordinate at most H = 3.061e10, all on the critical line by Platt 2011, Theorem 2.4 a. Partial
summation of the size of G of display 2.17 at one half plus i gamma against the Riemann von
Mangoldt count with Rosser's error, input b of Theorem 2.4 and d of Theorem 3.2 on page 11.
Uncertified mpmath values 0.00968638, 0.00587643, 0.00356505 and 1.0e-22, error bar at most
3.3e-12. Class HARD. -/
theorem endpoint_low_height_zero_sum_high_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => |ρ.1.im| ≤ 30610000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ highRowLowZeroBudgetS10 r.logIndex := by
  sorry

/-- LEAF: page 6 Theorem 2.4 a with the verified height 3e12 of Platt and Trudgian 2021, for
rows 58, 59, 60 and 150 of Table 2 on page 13: the zeros with ordinate between H = 3.061e10 and
3e12 lie on the critical line, so each term is at most the bound 2.28 of page 5 at real part one
half times X^(-1/2), and the count of display 2.47 with the Riemann von Mangoldt error bounds the
sum. Uncertified mpmath bound at most 1.5e-14 on each row. Class HARD. -/
theorem endpoint_mid_height_zero_sum_high_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000 ∧ |ρ.1.im| ≤ 3000000000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ 1 / 100000 := by
  sorry

/-- LEAF: page 9 display 2.59 and 2.60 with sigma0 = 1 and H = 3e12, for rows 58, 59, 60 and 150
of Table 2 on page 13: every zero above 3e12 is bounded by display 2.28 of page 5 with the
trivial factor X^(beta - 1) at most 1, and the sum of gamma^(-m-1) by S3 of display 2.47 at 3e12.
No zero density input is needed. Uncertified mpmath bound 2.4e-123 on rows 58 to 60 and
3.8e-129 on row 150. Class HARD. -/
theorem endpoint_top_height_zero_tail_high_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ 1 / 100000 := by
  sorry

/-- LEAF: page 9 display 2.64 at the row endpoint with the zero sum replaced by the three
budgets, a finite numeric check over rows 58, 59, 60 and 150 of Table 2 on page 13, using the
weight integrals and the nu term of page 9. Uncertified margins 0.05427, 0.04201, 0.03787 and
0.01801 in units of (e^u - 1) X. Class MEDIUM. -/
theorem endpoint_budget_numeric_high_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (highRowLowZeroBudgetS10 r.logIndex + 1 / 100000 + 1 / 100000)) := by
  sorry

/-- Assembly: the exact statement of table_endpoint_budget_high from the four leaves. -/
theorem table_endpoint_budget_high_split_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  have hL0 : 0 ≤ highRowLowZeroBudgetS10 r.logIndex := by
    simpa using endpoint_low_height_zero_sum_high_S10 hr hhigh ∅
  have hZ : zeroError r.m r.deltaQ r.uQ (rowEndpointX r) ≤
      highRowLowZeroBudgetS10 r.logIndex + 1 / 100000 + 1 / 100000 := by
    unfold zeroError
    refine tsum_le_of_sum_le' (by linarith) (fun s => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => |ρ.1.im| ≤ 30610000000)]
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000))
      (fun ρ => |ρ.1.im| ≤ 3000000000000)]
    rw [Finset.filter_filter]
    have h1 := endpoint_low_height_zero_sum_high_S10 hr hhigh s
    have h2 := endpoint_mid_height_zero_sum_high_S10 hr hhigh s
    have h3 := endpoint_top_height_zero_tail_high_S10 hr hhigh
      (s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000))
    linarith
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hX : 0 < rowEndpointX r := by
    unfold rowEndpointX
    have := Real.exp_pos (r.uQ : ℝ)
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
  refine (endpoint_budget_numeric_high_S10 hr hhigh).trans_le ?_
  apply mul_le_mul_of_nonneg_left _ hP.le
  linarith

#print axioms table_endpoint_budget_high_split_S10

end LeanLab.KadiriLumley2014.Task92
