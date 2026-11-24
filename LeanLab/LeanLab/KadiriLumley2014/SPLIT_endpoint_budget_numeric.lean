/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 9 display 2.64 and page 13 Table 2.
SPLIT of endpoint_budget_numeric from SPLIT_table_endpoint_budget_low.lean, by row,
ROUTE BURST S98 burst-20261122. Each row leaf is the page 9 display 2.64 check at the
endpoint of one printed row of Table 2, with the two per row zero budgets. The four rows
of log index 58, 59, 60 and 150 are excluded by the hypothesis log index at most 57.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_table_endpoint_budget_low

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-
Row log 4e18: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.58620, high budget 0.02561, remaining margin 0.27479 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log 4e18 on page 13, with the
zero sum replaced by the low budget 0.58620 plus the high budget 0.02561; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.27479. Class MEDIUM. -/
theorem endpoint_budget_numeric_row0 (r : PrintedRow) (hr : r = ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 43: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.57871, high budget 0.03815, remaining margin 0.26500 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 43 on page 13, with the
zero sum replaced by the low budget 0.57871 plus the high budget 0.03815; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.26500. Class MEDIUM. -/
theorem endpoint_budget_numeric_row43 (r : PrintedRow) (hr : r = ⟨43, 5, 33490, 291316980, 92, 2147, 38753947⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 44: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.56710, high budget 0.01118, remaining margin 0.30465 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 44 on page 13, with the
zero sum replaced by the low budget 0.56710 plus the high budget 0.01118; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.30465. Class MEDIUM. -/
theorem endpoint_budget_numeric_row44 (r : PrintedRow) (hr : r = ⟨44, 6, 23300, 488509984, 92, 2324, 61162616⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 45: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.54479, high budget 0.00764, remaining margin 0.32496 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 45 on page 13, with the
zero sum replaced by the low budget 0.54479 plus the high budget 0.00764; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.32496. Class MEDIUM. -/
theorem endpoint_budget_numeric_row45 (r : PrintedRow) (hr : r = ⟨45, 7, 16280, 797398875, 92, 2494, 95381241⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 46: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.51919, high budget 0.01257, remaining margin 0.33633 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 46 on page 13, with the
zero sum replaced by the low budget 0.51919 plus the high budget 0.01257; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.33633. Class MEDIUM. -/
theorem endpoint_budget_numeric_row46 (r : PrintedRow) (hr : r = ⟨46, 8, 11340, 1284120197, 92, 2651, 148306019⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 47: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.47893, high budget 0.03821, remaining margin 0.32344 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 47 on page 13, with the
zero sum replaced by the low budget 0.47893 plus the high budget 0.03821; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.32344. Class MEDIUM. -/
theorem endpoint_budget_numeric_row47 (r : PrintedRow) (hr : r = ⟨47, 9, 8080, 1996029891, 92, 2836, 227619375⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 48: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.44157, high budget 0.03820, remaining margin 0.34368 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 48 on page 13, with the
zero sum replaced by the low budget 0.44157 plus the high budget 0.03820; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.34368. Class MEDIUM. -/
theorem endpoint_budget_numeric_row48 (r : PrintedRow) (hr : r = ⟨48, 11, 6000, 3204848430, 93, 3050, 346582570⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 49: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.40912, high budget 0.01473, remaining margin 0.41037 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 49 on page 13, with the
zero sum replaced by the low budget 0.40912 plus the high budget 0.01473; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.41037. Class MEDIUM. -/
theorem endpoint_budget_numeric_row49 (r : PrintedRow) (hr : r = ⟨49, 15, 4682, 5415123831, 93, 3275, 518958776⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 50: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.35074, high budget 0.02260, remaining margin 0.42702 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 50 on page 13, with the
zero sum replaced by the low budget 0.35074 plus the high budget 0.02260; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.42702. Class MEDIUM. -/
theorem endpoint_budget_numeric_row50 (r : PrintedRow) (hr : r = ⟨50, 20, 3889, 8466793105, 93, 3543, 753575355⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 51: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.27324, high budget 0.03496, remaining margin 0.41318 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 51 on page 13, with the
zero sum replaced by the low budget 0.27324 plus the high budget 0.03496; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.41318. Class MEDIUM. -/
theorem endpoint_budget_numeric_row51 (r : PrintedRow) (hr : r = ⟨51, 28, 3625, 12399463961, 93, 3849, 1037917449⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 52: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.18750, high budget 0.04548, remaining margin 0.34622 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 52 on page 13, with the
zero sum replaced by the low budget 0.18750 plus the high budget 0.04548; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.34622. Class MEDIUM. -/
theorem endpoint_budget_numeric_row52 (r : PrintedRow) (hr : r = ⟨52, 39, 3803, 16139006408, 93, 4127, 1313524036⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 53: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.11754, high budget 0.05308, remaining margin 0.23918 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 53 on page 13, with the
zero sum replaced by the low budget 0.11754 plus the high budget 0.05308; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.23918. Class MEDIUM. -/
theorem endpoint_budget_numeric_row53 (r : PrintedRow) (hr : r = ⟨53, 48, 4088, 18290358817, 93, 4301, 1524171138⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 54: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.07173, high budget 0.05622, remaining margin 0.14562 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 54 on page 13, with the
zero sum replaced by the low budget 0.07173 plus the high budget 0.05622; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.14562. Class MEDIUM. -/
theorem endpoint_budget_numeric_row54 (r : PrintedRow) (hr : r = ⟨54, 54, 4311, 19412056863, 93, 4398, 1670398039⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 55: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.04355, high budget 0.05902, remaining margin 0.07792 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 55 on page 13, with the
zero sum replaced by the low budget 0.04355 plus the high budget 0.05902; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.07792. Class MEDIUM. -/
theorem endpoint_budget_numeric_row55 (r : PrintedRow) (hr : r = ⟨55, 56, 4386, 19757119193, 93, 4445, 1770251249⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 56: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.02638, high budget 0.05819, remaining margin 0.03827 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 56 on page 13, with the
zero sum replaced by the low budget 0.02638 plus the high budget 0.05819; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.03827. Class MEDIUM. -/
theorem endpoint_budget_numeric_row56 (r : PrintedRow) (hr : r = ⟨56, 59, 4508, 20210075547, 93, 4481, 1838818070⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

/-
Row log index 57: uncertified mpmath falsifier, notes/burst-20261115/scripts/actualzeros_rows,
low budget 0.01602, high budget 0.05926, remaining margin 0.01069 in units of the factor
(e^u - 1) X of the right side.
-/
/-- LEAF: page 9 display 2.64 at the endpoint of the Table 2 row log index 57 on page 13, with the
zero sum replaced by the low budget 0.01602 plus the high budget 0.05926; weight integrals and nu
of page 9 evaluated for m of this row. Uncertified margin 0.01069. Class MEDIUM. -/
theorem endpoint_budget_numeric_row57 (r : PrintedRow) (hr : r = ⟨57, 59, 4506, 20219045843, 93, 4496, 1886389443⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  sorry

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
