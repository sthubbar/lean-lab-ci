/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 9 display 2.64 and page 13 Table 2.
SPLIT of endpoint_budget_numeric from SPLIT_table_endpoint_budget_low.lean, by row,
ROUTE BURST S98 burst-20261122. Each row leaf is the page 9 display 2.64 check at the
endpoint of one printed row of Table 2, with the two per row zero budgets. The four rows
of log index 58, 59, 60 and 150 are excluded by the hypothesis log index at most 57.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_table_endpoint_budget_low
import LeanLab.KadiriLumley2014.EndpointRowsS153

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-
Row log 4e18: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.58620, high budget 0.02561, remaining margin 0.27479 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log 4e18 on page 13, with the
zero sum replaced by the low budget 0.58620 plus the high budget 0.02561; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.27479. Class MEDIUM. -/
theorem endpoint_budget_numeric_row0 (r : PrintedRow) (hr : r = ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 35800 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 35800 / 10 ^ 12 / 5 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((2130 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 5 := by subst hr; rfl
  have hL : r.logIndex = 0 := by subst hr; rfl
  have hT : r.threshold = (4 * 10 ^ 18 : ℝ) := by
    subst hr; simp [PrintedRow.threshold, evenBase]; norm_num
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 5 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 5 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 5 (2130 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((15917/500000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_5_2129
    have hP1 := rowWPrim_one_pos_5
    have : 2 * rowWPrim 5 (2130 / 10000) ≤ 15917/500000 * rowWPrim 5 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.58620 + 0.02561 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((15917/500000 : ℚ) : ℝ)) (LT := ((857 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (LTlo := ((856 : ℕ) : ℝ) / ((20 : ℕ) : ℝ))
    (Y := 139664811) (KY := ((376 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 9) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; norm_num
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_5
  · norm_num
  · rw [hT]
    have h := log_le_of_pow_le_rat_S153 (y := 4 * 10 ^ 18) (n := 857) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · rw [hT]
    have h := le_log_of_le_pow_rat_S153 (y := 4 * 10 ^ 18) (n := 856) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 139664811) (n := 376) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]; norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 43: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.57871, high budget 0.03815, remaining margin 0.26500 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 43 on page 13, with the
zero sum replaced by the low budget 0.57871 plus the high budget 0.03815; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.26500. Class MEDIUM. -/
theorem endpoint_budget_numeric_row43 (r : PrintedRow) (hr : r = ⟨43, 5, 33490, 291316980, 92, 2147, 38753947⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 33490 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 33490 / 10 ^ 12 / 5 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((2148 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 5 := by subst hr; rfl
  have hL : r.logIndex = 43 := by subst hr; rfl
  have hT : r.threshold = Real.exp 43 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 5 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 5 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 5 (2148 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((1327/40000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_5_2147
    have hP1 := rowWPrim_one_pos_5
    have : 2 * rowWPrim 5 (2148 / 10000) ≤ 1327/40000 * rowWPrim 5 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.57871 + 0.03815 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((1327/40000 : ℚ) : ℝ)) (LT := 43) (LTlo := 43)
    (Y := 149298304) (KY := ((377 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 9) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_5
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 149298304) (n := 377) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 43
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 44: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.56710, high budget 0.01118, remaining margin 0.30465 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 44 on page 13, with the
zero sum replaced by the low budget 0.56710 plus the high budget 0.01118; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.30465. Class MEDIUM. -/
theorem endpoint_budget_numeric_row44 (r : PrintedRow) (hr : r = ⟨44, 6, 23300, 488509984, 92, 2324, 61162616⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 23300 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 23300 / 10 ^ 12 / 6 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((2325 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 6 := by subst hr; rfl
  have hL : r.logIndex = 44 := by subst hr; rfl
  have hT : r.threshold = Real.exp 44 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 6 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 6 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 6 (2325 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((3273/100000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_6_2324
    have hP1 := rowWPrim_one_pos_6
    have : 2 * rowWPrim 6 (2325 / 10000) ≤ 3273/100000 * rowWPrim 6 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.56710 + 0.01118 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((3273/100000 : ℚ) : ℝ)) (LT := 44) (LTlo := 44)
    (Y := 257510737) (KY := ((388 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 9) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_6
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 257510737) (n := 388) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 44
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 45: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.54479, high budget 0.00764, remaining margin 0.32496 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 45 on page 13, with the
zero sum replaced by the low budget 0.54479 plus the high budget 0.00764; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.32496. Class MEDIUM. -/
theorem endpoint_budget_numeric_row45 (r : PrintedRow) (hr : r = ⟨45, 7, 16280, 797398875, 92, 2494, 95381241⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 16280 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 16280 / 10 ^ 12 / 7 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((2495 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 7 := by subst hr; rfl
  have hL : r.logIndex = 45 := by subst hr; rfl
  have hT : r.threshold = Real.exp 45 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 7 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 7 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 7 (2495 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((34183/1000000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_7_2494
    have hP1 := rowWPrim_one_pos_7
    have : 2 * rowWPrim 7 (2495 / 10000) ≤ 34183/1000000 * rowWPrim 7 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.54479 + 0.00764 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((34183/1000000 : ℚ) : ℝ)) (LT := 45) (LTlo := 45)
    (Y := 429975438) (KY := ((398 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 9) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_7
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 429975438) (n := 398) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 45
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 46: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.51919, high budget 0.01257, remaining margin 0.33633 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 46 on page 13, with the
zero sum replaced by the low budget 0.51919 plus the high budget 0.01257; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.33633. Class MEDIUM. -/
theorem endpoint_budget_numeric_row46 (r : PrintedRow) (hr : r = ⟨46, 8, 11340, 1284120197, 92, 2651, 148306019⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 11340 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 11340 / 10 ^ 12 / 8 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((2652 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 8 := by subst hr; rfl
  have hL : r.logIndex = 46 := by subst hr; rfl
  have hT : r.threshold = Real.exp 46 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 8 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 8 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 8 (2652 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((18351/500000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_8_2651
    have hP1 := rowWPrim_one_pos_8
    have : 2 * rowWPrim 8 (2652 / 10000) ≤ 18351/500000 * rowWPrim 8 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.51919 + 0.01257 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((18351/500000 : ℚ) : ℝ)) (LT := 46) (LTlo := 46)
    (Y := 705467382) (KY := ((408 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 9) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_8
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 705467382) (n := 408) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 46
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 47: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.47893, high budget 0.03821, remaining margin 0.32344 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 47 on page 13, with the
zero sum replaced by the low budget 0.47893 plus the high budget 0.03821; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.32344. Class MEDIUM. -/
theorem endpoint_budget_numeric_row47 (r : PrintedRow) (hr : r = ⟨47, 9, 8080, 1996029891, 92, 2836, 227619375⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 8080 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 8080 / 10 ^ 12 / 9 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((2837 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 9 := by subst hr; rfl
  have hL : r.logIndex = 47 := by subst hr; rfl
  have hT : r.threshold = Real.exp 47 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 9 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 9 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 9 (2837 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((22171/500000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_9_2836
    have hP1 := rowWPrim_one_pos_9
    have : 2 * rowWPrim 9 (2837 / 10000) ≤ 22171/500000 * rowWPrim 9 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.47893 + 0.03821 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((22171/500000 : ℚ) : ℝ)) (LT := 47) (LTlo := 47)
    (Y := 1113861397) (KY := ((417 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 9) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_9
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 1113861397) (n := 417) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 47
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 48: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.44157, high budget 0.03820, remaining margin 0.34368 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 48 on page 13, with the
zero sum replaced by the low budget 0.44157 plus the high budget 0.03820; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.34368. Class MEDIUM. -/
theorem endpoint_budget_numeric_row48 (r : PrintedRow) (hr : r = ⟨48, 11, 6000, 3204848430, 93, 3050, 346582570⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 6000 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 6000 / 10 ^ 12 / 11 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((3051 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 11 := by subst hr; rfl
  have hL : r.logIndex = 48 := by subst hr; rfl
  have hT : r.threshold = Real.exp 48 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 11 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 11 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 11 (3051 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((49011/1000000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_11_3050
    have hP1 := rowWPrim_one_pos_11
    have : 2 * rowWPrim 11 (3051 / 10000) ≤ 49011/1000000 * rowWPrim 11 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.44157 + 0.03820 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((49011/1000000 : ℚ) : ℝ)) (LT := 48) (LTlo := 48)
    (Y := 1833333346) (KY := ((427 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 10) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_11
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 1833333346) (n := 427) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 48
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 49: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.40912, high budget 0.01473, remaining margin 0.41037 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 49 on page 13, with the
zero sum replaced by the low budget 0.40912 plus the high budget 0.01473; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.41037. Class MEDIUM. -/
theorem endpoint_budget_numeric_row49 (r : PrintedRow) (hr : r = ⟨49, 15, 4682, 5415123831, 93, 3275, 518958776⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 4682 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 4682 / 10 ^ 12 / 15 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((3276 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 15 := by subst hr; rfl
  have hL : r.logIndex = 49 := by subst hr; rfl
  have hT : r.threshold = Real.exp 49 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 15 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 15 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 15 (3276 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((45823/1000000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_15_3275
    have hP1 := rowWPrim_one_pos_15
    have : 2 * rowWPrim 15 (3276 / 10000) ≤ 45823/1000000 * rowWPrim 15 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.40912 + 0.01473 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((45823/1000000 : ℚ) : ℝ)) (LT := 49) (LTlo := 49)
    (Y := 3203759094) (KY := ((438 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 10) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_15
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 3203759094) (n := 438) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 49
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 50: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.35074, high budget 0.02260, remaining margin 0.42702 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 50 on page 13, with the
zero sum replaced by the low budget 0.35074 plus the high budget 0.02260; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.42702. Class MEDIUM. -/
theorem endpoint_budget_numeric_row50 (r : PrintedRow) (hr : r = ⟨50, 20, 3889, 8466793105, 93, 3543, 753575355⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 3889 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 3889 / 10 ^ 12 / 20 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((3544 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 20 := by subst hr; rfl
  have hL : r.logIndex = 50 := by subst hr; rfl
  have hT : r.threshold = Real.exp 50 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 20 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 20 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 20 (3544 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((55139/1000000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_20_3543
    have hP1 := rowWPrim_one_pos_20
    have : 2 * rowWPrim 20 (3544 / 10000) ≤ 55139/1000000 * rowWPrim 20 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.35074 + 0.02260 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((55139/1000000 : ℚ) : ℝ)) (LT := 50) (LTlo := 50)
    (Y := 5142710230) (KY := ((448 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 10) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_20
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 5142710230) (n := 448) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 50
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 51: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.27324, high budget 0.03496, remaining margin 0.41318 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 51 on page 13, with the
zero sum replaced by the low budget 0.27324 plus the high budget 0.03496; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.41318. Class MEDIUM. -/
theorem endpoint_budget_numeric_row51 (r : PrintedRow) (hr : r = ⟨51, 28, 3625, 12399463961, 93, 3849, 1037917449⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 3625 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 3625 / 10 ^ 12 / 28 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((3850 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 28 := by subst hr; rfl
  have hL : r.logIndex = 51 := by subst hr; rfl
  have hT : r.threshold = Real.exp 51 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 28 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 28 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 28 (3850 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((77081/1000000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_28_3849
    have hP1 := rowWPrim_one_pos_28
    have : 2 * rowWPrim 28 (3850 / 10000) ≤ 77081/1000000 * rowWPrim 28 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.27324 + 0.03496 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((77081/1000000 : ℚ) : ℝ)) (LT := 51) (LTlo := 51)
    (Y := 7724137961) (KY := ((456 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 10) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_28
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 7724137961) (n := 456) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 51
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 52: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.18750, high budget 0.04548, remaining margin 0.34622 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 52 on page 13, with the
zero sum replaced by the low budget 0.18750 plus the high budget 0.04548; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.34622. Class MEDIUM. -/
theorem endpoint_budget_numeric_row52 (r : PrintedRow) (hr : r = ⟨52, 39, 3803, 16139006408, 93, 4127, 1313524036⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 3803 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 3803 / 10 ^ 12 / 39 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((4128 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 39 := by subst hr; rfl
  have hL : r.logIndex = 52 := by subst hr; rfl
  have hT : r.threshold = Real.exp 52 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 39 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 39 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 39 (4128 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((7319/62500 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_39_4127
    have hP1 := rowWPrim_one_pos_39
    have : 2 * rowWPrim 39 (4128 / 10000) ≤ 7319/62500 * rowWPrim 39 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.18750 + 0.04548 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((7319/62500 : ℚ) : ℝ)) (LT := 52) (LTlo := 52)
    (Y := 10255061834) (KY := ((462 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 10) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_39
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 10255061834) (n := 462) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 52
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 53: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.11754, high budget 0.05308, remaining margin 0.23918 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 53 on page 13, with the
zero sum replaced by the low budget 0.11754 plus the high budget 0.05308; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.23918. Class MEDIUM. -/
theorem endpoint_budget_numeric_row53 (r : PrintedRow) (hr : r = ⟨53, 48, 4088, 18290358817, 93, 4301, 1524171138⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 4088 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 4088 / 10 ^ 12 / 48 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((4302 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 48 := by subst hr; rfl
  have hL : r.logIndex = 53 := by subst hr; rfl
  have hT : r.threshold = Real.exp 53 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 48 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 48 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 48 (4302 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((165979/1000000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_48_4301
    have hP1 := rowWPrim_one_pos_48
    have : 2 * rowWPrim 48 (4302 / 10000) ≤ 165979/1000000 * rowWPrim 48 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.11754 + 0.05308 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((165979/1000000 : ℚ) : ℝ)) (LT := 53) (LTlo := 53)
    (Y := 11741683024) (KY := ((464 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 11) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_48
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 11741683024) (n := 464) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 53
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 54: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.07173, high budget 0.05622, remaining margin 0.14562 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 54 on page 13, with the
zero sum replaced by the low budget 0.07173 plus the high budget 0.05622; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.14562. Class MEDIUM. -/
theorem endpoint_budget_numeric_row54 (r : PrintedRow) (hr : r = ⟨54, 54, 4311, 19412056863, 93, 4398, 1670398039⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 4311 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 4311 / 10 ^ 12 / 54 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((4399 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 54 := by subst hr; rfl
  have hL : r.logIndex = 54 := by subst hr; rfl
  have hT : r.threshold = Real.exp 54 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 54 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 54 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 54 (4399 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((206809/1000000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_54_4398
    have hP1 := rowWPrim_one_pos_54
    have : 2 * rowWPrim 54 (4399 / 10000) ≤ 206809/1000000 * rowWPrim 54 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.07173 + 0.05622 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((206809/1000000 : ℚ) : ℝ)) (LT := 54) (LTlo := 54)
    (Y := 12526096089) (KY := ((466 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 11) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_54
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 12526096089) (n := 466) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 54
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 55: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.04355, high budget 0.05902, remaining margin 0.07792 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 55 on page 13, with the
zero sum replaced by the low budget 0.04355 plus the high budget 0.05902; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.07792. Class MEDIUM. -/
theorem endpoint_budget_numeric_row55 (r : PrintedRow) (hr : r = ⟨55, 56, 4386, 19757119193, 93, 4445, 1770251249⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 4386 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 4386 / 10 ^ 12 / 56 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((4446 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 56 := by subst hr; rfl
  have hL : r.logIndex = 55 := by subst hr; rfl
  have hT : r.threshold = Real.exp 55 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 56 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 56 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 56 (4446 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((118191/500000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_56_4445
    have hP1 := rowWPrim_one_pos_56
    have : 2 * rowWPrim 56 (4446 / 10000) ≤ 118191/500000 * rowWPrim 56 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.04355 + 0.05902 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((118191/500000 : ℚ) : ℝ)) (LT := 55) (LTlo := 55)
    (Y := 12767897914) (KY := ((466 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 11) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_56
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 12767897914) (n := 466) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 55
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 56: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.02638, high budget 0.05819, remaining margin 0.03827 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 56 on page 13, with the
zero sum replaced by the low budget 0.02638 plus the high budget 0.05819; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.03827. Class MEDIUM. -/
theorem endpoint_budget_numeric_row56 (r : PrintedRow) (hr : r = ⟨56, 59, 4508, 20210075547, 93, 4481, 1838818070⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 4508 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 4508 / 10 ^ 12 / 59 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((4482 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 59 := by subst hr; rfl
  have hL : r.logIndex = 56 := by subst hr; rfl
  have hT : r.threshold = Real.exp 56 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 59 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 59 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 59 (4482 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((128067/500000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_59_4481
    have hP1 := rowWPrim_one_pos_59
    have : 2 * rowWPrim 59 (4482 / 10000) ≤ 128067/500000 * rowWPrim 59 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.02638 + 0.05819 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((128067/500000 : ℚ) : ℝ)) (LT := 56) (LTlo := 56)
    (Y := 13087843894) (KY := ((466 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 11) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_59
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 13087843894) (n := 466) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 56
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

/-
Row log index 57: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.01602, high budget 0.05926, remaining margin 0.01069 in units of the factor
(e^u - 1) X of the right side.
-/
/-- PROVED in burst S153, was a LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 57 on page 13, with the
zero sum replaced by the low budget 0.01602 plus the high budget 0.05926; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.01069. Class MEDIUM. -/
theorem endpoint_budget_numeric_row57 (r : PrintedRow) (hr : r = ⟨57, 59, 4506, 20219045843, 93, 4496, 1886389443⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  have hδv : ((r.deltaQ : ℚ) : ℝ) = 4506 / 10 ^ 12 := by
    subst hr; simp only [PrintedRow.deltaQ]; push_cast; norm_num
  have huv : ((r.uQ : ℚ) : ℝ) = 4506 / 10 ^ 12 / 59 := by
    subst hr; simp only [PrintedRow.uQ, PrintedRow.deltaQ]; push_cast; norm_num
  have hav : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = ((4497 / 10000 : ℚ) : ℝ) := by
    subst hr; simp only [PrintedRow.aQ]; push_cast; norm_num
  have hm : r.m = 59 := by subst hr; rfl
  have hL : r.logIndex = 57 := by subst hr; rfl
  have hT : r.threshold = Real.exp 57 := by
    subst hr; simp [PrintedRow.threshold]
  have hI : ∫ t in (0 : ℝ)..1, weight r.m t = ((rowWPrim 59 1 : ℚ) : ℝ) := by
    rw [hm]; have := integral_weight_eq_rowWPrim 59 1; push_cast at this; exact this
  have hν : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) = 2 * ((rowWPrim 59 (4497 / 10000) : ℚ) : ℝ) := by
    rw [hm, hav, tailMass_eq_two, integral_weight_eq_rowWPrim]
  have hνq : tailMass r.m ((r.aQ : ℝ) + 1 / 10000) ≤
      ((135117/500000 : ℚ) : ℝ) * ∫ t in (0 : ℝ)..1, weight r.m t := by
    rw [hν, hI]
    have hP := row_nu_ratio_59_4496
    have hP1 := rowWPrim_one_pos_59
    have : 2 * rowWPrim 59 (4497 / 10000) ≤ 135117/500000 * rowWPrim 59 1 := by
      rw [div_le_iff₀ hP1] at hP; exact hP
    exact_mod_cast this
  have hB : lowZeroBudget r.logIndex + highZeroBudget r.logIndex = 0.01602 + 0.05926 := by
    rw [hL]; simp only [lowZeroBudget, highZeroBudget]
  rw [hB]
  refine row_closer_S153 (T := r.threshold) (q := ((135117/500000 : ℚ) : ℝ)) (LT := 57) (LTlo := 57)
    (Y := 13093652968) (KY := ((466 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) (s0 := 10 ^ 12) ?_ ?_ ?_ ?_ rfl ?_ ?_ hνq ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hδv]; norm_num
  · rw [hδv]; norm_num
  · rw [huv]; norm_num
  · rw [huv]; norm_num
  · rw [hT]; exact Real.one_le_exp (by norm_num)
  · rw [hI]; exact_mod_cast rowWPrim_one_pos_59
  · norm_num
  · rw [hT, Real.log_exp]
  · rw [hT, Real.log_exp]
  · rw [hδv, huv]; norm_num
  · have h := log_le_of_pow_le_rat_S153 (y := 13093652968) (n := 466) (k := 20) (by norm_num) (by norm_num)
      (by decide +kernel)
    push_cast at h; exact h
  · norm_num
  · norm_num
  · rw [hT]
    have he := exp_nat_ge_S153 57
    push_cast at he
    refine le_trans ?_ he
    norm_num
  · norm_num
  · rw [hδv, huv]; norm_num

theorem endpoint_budget_numeric_split {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  simp only [tableTwo, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact endpoint_budget_numeric_row0 _ rfl
  · exact endpoint_budget_numeric_row43 _ rfl
  · exact endpoint_budget_numeric_row44 _ rfl
  · exact endpoint_budget_numeric_row45 _ rfl
  · exact endpoint_budget_numeric_row46 _ rfl
  · exact endpoint_budget_numeric_row47 _ rfl
  · exact endpoint_budget_numeric_row48 _ rfl
  · exact endpoint_budget_numeric_row49 _ rfl
  · exact endpoint_budget_numeric_row50 _ rfl
  · exact endpoint_budget_numeric_row51 _ rfl
  · exact endpoint_budget_numeric_row52 _ rfl
  · exact endpoint_budget_numeric_row53 _ rfl
  · exact endpoint_budget_numeric_row54 _ rfl
  · exact endpoint_budget_numeric_row55 _ rfl
  · exact endpoint_budget_numeric_row56 _ rfl
  · exact endpoint_budget_numeric_row57 _ rfl
  all_goals (exfalso; norm_num at hlow)

end LeanLab.KadiriLumley2014.Task92
