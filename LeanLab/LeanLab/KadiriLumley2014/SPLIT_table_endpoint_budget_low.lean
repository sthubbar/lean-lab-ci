/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 4 display 2.20, page 9 Theorem 2.7
and page 13 Table 2. SPLIT of table_endpoint_budget_low from SPLIT_table_endpoint_budget.lean,
ROUTE BURST S98 burst-20261122.
The zero sum zeroError is split at the verified height H = 3.061e10 of Platt 2011 into
the zeros with absolute ordinate at most H and the rest, each bounded by a per row budget.
The budgets are the point iii values SigmaLow and SigmaHigh_CORRECTED of the uncertified
mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows/row_00 to row_15.json,
each rounded up at the fifth decimal and then raised by 1e-5.
Per row, log index, low budget, high budget, remaining numeric margin:
  log 4e18 0.58620 0.02561 0.27479,  43 0.57871 0.03815 0.26500,
  44 0.56710 0.01118 0.30465,  45 0.54479 0.00764 0.32496,
  46 0.51919 0.01257 0.33633,  47 0.47893 0.03821 0.32344,
  48 0.44157 0.03820 0.34368,  49 0.40912 0.01473 0.41037,
  50 0.35074 0.02260 0.42702,  51 0.27324 0.03496 0.41318,
  52 0.18750 0.04548 0.34622,  53 0.11754 0.05308 0.23918,
  54 0.07173 0.05622 0.14562,  55 0.04355 0.05902 0.07792,
  56 0.02638 0.05819 0.03827,  57 0.01602 0.05926 0.01069.
The margin is the falsifier's budget_before_zero_sum minus both budgets, in units of
the factor (e^u - 1) X of the right side.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_table_endpoint_budget
import LeanLab.KadiriLumley2014.PROVE_table_numeric_env_high

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- Per row budget for the zeros of ordinate at most H, by log index; data only. -/
noncomputable def lowZeroBudget : ℕ → ℝ
  | 0 => 0.58620 | 43 => 0.57871 | 44 => 0.56710 | 45 => 0.54479
  | 46 => 0.51919 | 47 => 0.47893 | 48 => 0.44157 | 49 => 0.40912
  | 50 => 0.35074 | 51 => 0.27324 | 52 => 0.18750 | 53 => 0.11754
  | 54 => 0.07173 | 55 => 0.04355 | 56 => 0.02638 | 57 => 0.01602
  | _ => 0

/-- Per row budget for the zeros of ordinate above H, by log index; data only. -/
noncomputable def highZeroBudget : ℕ → ℝ
  | 0 => 0.02561 | 43 => 0.03815 | 44 => 0.01118 | 45 => 0.00764
  | 46 => 0.01257 | 47 => 0.03821 | 48 => 0.03820 | 49 => 0.01473
  | 50 => 0.02260 | 51 => 0.03496 | 52 => 0.04548 | 53 => 0.05308
  | 54 => 0.05622 | 55 => 0.05902 | 56 => 0.05819 | 57 => 0.05926
  | _ => 0

/-- The numeric check for one of the rows with positive log index.  This is the
elementary rational calculation used in `endpoint_budget_numeric`. -/
theorem numeric_low_of_row_S10e {r : PrintedRow} (hr : r ∈ tableTwo)
    (hL0 : r.logIndex ≠ 0) (c s bQ : ℚ) (hs0 : 0 < s)
    (hratio : 2 * (∑ k ∈ range (r.m + 1), (-1 : ℚ) ^ k *
        ((r.m.factorial / (k.factorial * (r.m - k).factorial) : ℕ) : ℚ) *
        ((r.aQ + 1 / 10000) ^ (r.m + k + 1) / ((r.m + k + 1 : ℕ) : ℚ))) *
        ((2 * r.m + 1).factorial : ℚ) ≤ c * (r.m.factorial : ℚ) ^ 2)
    (hu34 : 1 / 2 ^ 34 ≤ r.uQ) (hu1 : r.uQ < 1)
    (hsX : s ^ 2 * (1 + r.deltaQ) ≤ (2718 / 1000) ^ r.logIndex * (1 - r.uQ))
    (hell : 0 < (r.logIndex : ℚ) - r.uQ - r.deltaQ - 34 * (6931471808 / 10 ^ 10))
    (hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = (bQ : ℝ))
    (hnum : (205022 / 10 ^ 8 : ℚ) / (r.uQ * s) +
        2 * (1 + r.deltaQ) * r.logIndex * c /
          ((r.logIndex : ℚ) - r.uQ - r.deltaQ - 34 * (6931471808 / 10 ^ 10)) +
        1 / (2 * s ^ 4) < 1 + r.deltaQ / 2 - bQ) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hs := table_small_steps r hr
  have hrt := tableTwo_rounding_arithmetic r hr
  have hrat := tail_ratio_le_of_rat_S10e r.m (r.aQ + 1 / 10000) c hratio
  push_cast at hrat
  have hR0 : 0 ≤ tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
      (∫ t in (0 : ℝ)..1, weight r.m t) := by
    have ha0 : (0 : ℝ) ≤ (r.aQ : ℝ) + 1 / 10000 := by
      have : (0 : ℝ) ≤ ((r.aQ : ℚ) : ℝ) := by exact_mod_cast hrt.1.2.2.2.1
      linarith
    have ha2 : (r.aQ : ℝ) + 1 / 10000 ≤ 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hrt.1.2.2.2.2.1
      push_cast at this
      exact this
    exact (tailMass_ratio_bounds r.m ha0 ha2).1
  have hXeq : rowEndpointX r =
      Real.exp (r.logIndex : ℝ) / (Real.exp (r.uQ : ℝ) * (1 + (r.deltaQ : ℝ))) := by
    unfold rowEndpointX PrintedRow.threshold
    rw [if_neg hL0]
  have hKeq : (2.05022 * 10 ^ (-3 : ℤ) : ℝ) = ((205022 / 10 ^ 8 : ℚ) : ℝ) := by norm_num
  rw [mul_div_assoc, hKeq]
  have f1 : (1 : ℝ) / 2 ^ 34 ≤ (r.uQ : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hu34
    push_cast at this
    exact this
  have f2 : (r.uQ : ℝ) < 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hu1
    push_cast at this
    exact this
  have f3 : (s : ℝ) ^ 2 * (1 + (r.deltaQ : ℝ)) ≤
      (2718 / 1000 : ℝ) ^ r.logIndex * (1 - (r.uQ : ℝ)) := by
    have := (Rat.cast_le (K := ℝ)).mpr hsX
    push_cast at this
    exact this
  have f4 : 0 < (r.logIndex : ℝ) - (r.uQ : ℝ) - (r.deltaQ : ℝ) -
      34 * (6931471808 / 10 ^ 10) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hell
    push_cast at this
    exact this
  have f5 : (0 : ℝ) ≤ (r.deltaQ : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hs.1.le
    push_cast at this
    exact this
  have f6 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
  refine budget_from_facts_S10e (δ := (r.deltaQ : ℝ)) (u := (r.uQ : ℝ))
    (s := (s : ℝ)) (c := (c : ℝ)) (L := (r.logIndex : ℝ)) (n := r.logIndex) rfl hXeq
    f5 f1 f2 f6 f3 f4 hR0 hrat (by norm_num) ?_
  rw [hB]
  have h := (Rat.cast_lt (K := ℝ)).mpr hnum
  push_cast at h ⊢
  linarith

/-- LEAF: page 4 display 2.20, the zeros with ordinate at most H = 3.061e10, all on the
critical line by Platt 2011. Partial summation of the size of G of display 2.17 at one half
plus i gamma against the Riemann von Mangoldt count with Rosser's error, input d of
Theorem 3.2 on page 11. Uncertified mpmath value row 57 0.0160007, log 4e18 0.586181,
error bar at most 6.4e-9. Class HARD. -/
theorem endpoint_low_height_zero_sum {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => |ρ.1.im| ≤ 30610000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ lowZeroBudget r.logIndex := by
  sorry

/-- LEAF: pages 7 to 9, the zeros with ordinate above H = 3.061e10, bounded by B3 of
display 2.39, B42 and B41 of Lemma 2.6 with S5 of display 2.44 corrected to R0 over
log X0 as in the Faber and Kadiri corrigendum, zero free region and density input of
Theorem 3.2. Uncertified mpmath value row 57 0.0592478, log 4e18 0.0255956. Class HARD. -/
theorem endpoint_high_height_zero_tail {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ highZeroBudget r.logIndex := by
  sorry

/-- LEAF: page 9 display 2.64 at the row endpoint with the zero sum replaced by the two
per row budgets, a finite numeric check over sixteen rows of Table 2 on page 13, using
the weight integrals and the nu term of page 9. Uncertified margin 0.01069 at row 57,
0.27479 at log 4e18, in units of (e^u - 1) X. Class MEDIUM. -/
theorem endpoint_budget_numeric {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

theorem table_endpoint_budget_low_split {r : PrintedRow} (hr : r ∈ tableTwo)
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
  refine (endpoint_budget_numeric hr hlow).trans_le ?_
  apply mul_le_mul_of_nonneg_left _ hP.le
  linarith

end LeanLab.KadiriLumley2014.Task92
