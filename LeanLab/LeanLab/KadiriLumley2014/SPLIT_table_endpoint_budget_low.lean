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
  simp only [tableTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
  (try contradiction) <;>
  (try norm_num [PrintedRow.deltaQ, PrintedRow.aQ, PrintedRow.uQ, PrintedRow.threshold, rowEndpointX,
    lowZeroBudget, highZeroBudget, tailCoefficient, tailMass, weight, weight_mass,
    intervalFraction, Real.exp_neg, Real.exp_log, Real.log_mul, Real.log_div,
    Real.log_rpow, Real.log_pow, Real.sqrt_eq_iff_sq_eq, Real.exp_one_lt_d9, Real.exp_one_gt_d9,
    Real.add_one_le_exp, Real.exp_pos, Real.log_lt_log_iff, Real.log_le_log_iff] at hlow ⊢) <;>
  (try
    {
      -- Use exact weight_mass formula
      have h₁ : (∫ t in (0 : ℝ)..1, (weight (5 : ℕ) t : ℝ)) = (2 : ℝ) ^ (2 * (5 : ℕ)) * ((5 : ℕ).factorial : ℝ) ^ 2 / ((2 * (5 : ℕ) + 1 : ℕ).factorial : ℝ) := by
        rw [weight_mass]
        <;> norm_num
      -- Use tailMass bound
      have h₂ : tailMass (5 : ℕ) ((2129 : ℝ) / 10000 + 1 / 10000) ≤ 2 * ((2130 : ℝ) / 10000) * (4 * ((2130 : ℝ) / 10000) * (1 - (2130 : ℝ) / 10000)) ^ (5 : ℕ) := by
        have h₃ : 0 ≤ ((2130 : ℝ) / 10000 : ℝ) := by norm_num
        have h₄ : ((2130 : ℝ) / 10000 : ℝ) ≤ 1 / 2 := by norm_num
        have h₅ : tailMass (5 : ℕ) ((2130 : ℝ) / 10000) ≤ 2 * ((2130 : ℝ) / 10000) * (4 * ((2130 : ℝ) / 10000) * (1 - (2130 : ℝ) / 10000)) ^ (5 : ℕ) := by
          apply tailMass_le_endpoint
          <;> norm_num at h₃ h₄ ⊢ <;> linarith
        have h₆ : tailMass (5 : ℕ) ((2129 : ℝ) / 10000 + 1 / 10000) = tailMass (5 : ℕ) ((2130 : ℝ) / 10000) := by norm_num
        rw [h₆]
        exact h₅
      -- Bound exp(38) for logIndex 0
      have h₇ : Real.exp (38 : ℝ) < (2.7182818286 : ℝ) ^ 38 := by
        have := Real.exp_one_lt_d9
        calc
          Real.exp (38 : ℝ) = (Real.exp 1) ^ 38 := by rw [← Real.exp_nat_mul]; norm_num
          _ < (2.7182818286 : ℝ) ^ 38 := by gcongr <;> norm_num
      have h₈ : Real.exp (38 : ℝ) > (2.7182818283 : ℝ) ^ 38 := by
        have := Real.exp_one_gt_d9
        calc
          (2.7182818283 : ℝ) ^ 38 < (Real.exp 1) ^ 38 := by gcongr <;> norm_num
          _ = Real.exp (38 : ℝ) := by rw [← Real.exp_nat_mul]; norm_num
      -- Bound exp(uQ) for small uQ
      have h₉ : Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) < 1 + (35800 / (5 * 10 ^ 12 : ℝ)) + (35800 / (5 * 10 ^ 12 : ℝ)) ^ 2 := by
        have h₉₁ : Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) ≤ 1 / (1 - (35800 / (5 * 10 ^ 12 : ℝ))) := by
          have h₉₂ : (35800 / (5 * 10 ^ 12 : ℝ) : ℝ) < 1 := by norm_num
          have h₉₃ : 0 ≤ (35800 / (5 * 10 ^ 12 : ℝ) : ℝ) := by positivity
          have h₉₄ : Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) ≤ 1 / (1 - (35800 / (5 * 10 ^ 12 : ℝ))) := by
            have h₉₅ := Real.exp_bound_div_one_sub_of_interval (by positivity) (by norm_num)
            exact h₉₅
          exact h₉₄
        have h₉₆ : (1 : ℝ) / (1 - (35800 / (5 * 10 ^ 12 : ℝ))) < 1 + (35800 / (5 * 10 ^ 12 : ℝ)) + (35800 / (5 * 10 ^ 12 : ℝ)) ^ 2 := by
          norm_num [div_lt_iff]
          <;> norm_num
          <;> linarith
        linarith
      have h₁₀ : Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) > 1 + (35800 / (5 * 10 ^ 12 : ℝ)) := by
        have h₁₀₁ : Real.add_one_le_exp (35800 / (5 * 10 ^ 12 : ℝ)) := by exact Real.add_one_le_exp _
        have h₁₀₂ : (1 : ℝ) + (35800 / (5 * 10 ^ 12 : ℝ)) < Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) := by
          linarith [Real.add_one_lt_exp (by positivity : (0 : ℝ) < (35800 / (5 * 10 ^ 12 : ℝ)))]
        linarith
      -- Bound log and sqrt
      norm_num [h₁, h₂, h₇, h₈, h₉, h₁₀] at hlow ⊢
      <;>
      (try linarith [Real.add_one_le_exp (0 : ℝ), Real.exp_pos (0 : ℝ)]) <;>
      (try nlinarith [Real.add_one_le_exp (0 : ℝ), Real.exp_pos (0 : ℝ)])
      <;>
      (try
        {
          -- For log bounds, use the fact that log is increasing
          have h₁₁ : Real.log ((4 * 10 ^ 18 : ℝ) / (Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) * (1 + (35800 : ℝ) / 10 ^ 12))) > 0 := by
            apply Real.log_pos
            have h₁₂ : (1 : ℝ) < (4 * 10 ^ 18 : ℝ) / (Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) * (1 + (35800 : ℝ) / 10 ^ 12)) := by
              have h₁₃ : Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) < 2 := by
                have h₁₄ : Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) < 1 + (35800 / (5 * 10 ^ 12 : ℝ)) + (35800 / (5 * 10 ^ 12 : ℝ)) ^ 2 := h₉
                norm_num at h₁₄ ⊢
                <;> linarith
              have h₁₅ : (Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) * (1 + (35800 : ℝ) / 10 ^ 12) : ℝ) < 4 := by
                norm_num at h₁₄ ⊢
                <;> nlinarith
              have h₁₆ : (4 * 10 ^ 18 : ℝ) / (Real.exp (35800 / (5 * 10 ^ 12 : ℝ)) * (1 + (35800 : ℝ) / 10 ^ 12)) > 1 := by
                apply (lt_div_iff₀ (by positivity)).mpr
                norm_num at h₁₅ ⊢
                <;> nlinarith
              linarith
            linarith
          norm_num at h₁₁ ⊢
          <;> linarith
        })
    }) <;>
  (try
    {
      -- Similar bounds for other rows
      norm_num at hlow ⊢
      <;>
      (try linarith [Real.add_one_le_exp (0 : ℝ), Real.exp_pos (0 : ℝ)]) <;>
      (try nlinarith [Real.add_one_le_exp (0 : ℝ), Real.exp_pos (0 : ℝ)])
    })
  <;>
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
