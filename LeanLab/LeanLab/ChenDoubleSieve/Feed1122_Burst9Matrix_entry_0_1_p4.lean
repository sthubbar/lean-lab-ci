import LeanLab.ChenDoubleSieve.Table1Algebra
import LeanLab.ChenDoubleSieve.KernelIntegrability

/-!
# Feed 1122, p4 split of the two half panel leaves of `Burst9Matrix.entry_0_1`

Source: Wu 2004, arXiv 0705.1652, display 7.1, kernel Xi2 of display 3.22, page 15, row 1 of
Table 1, parameters `s = 2.2`, `sp = 4.54`, `k1 = 3.53`, `k2 = 2.90`, `k3 = 2.44`.
On `[11/5, 23/10]` no window endpoint of display 3.22 falls inside the panel: the active terms are
the `σ₀` term and the four windows ending at `sp - 2 = 2.54`, so the kernel is smooth there.
Each half panel is cut at its midpoint, giving four quarter panels of width `1/40`.
Double precision Gauss Legendre values, 40 nodes on 2 subpanels:
`[11/5, 89/40]` 0.0064952756220, `[89/40, 9/4]` 0.0065320228138,
`[9/4, 91/40]` 0.0065661446811, `[91/40, 23/10]` 0.0065976249335.
Each quarter bound leaves `1.70e-8`, half of the half panel margin `3.40e-8`.
A monotone bound, minimum times width, loses `3.0e-5` to `3.8e-5` per quarter, far above the margin, since the kernel rises from
`0.2590` to `0.2645` across the panel,
so each quarter still needs a certified fine quadrature of `σ₀`.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_0_1_p4

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, quarter panel `[11/5, 89/40]`
of `a_{1,2}`: quadrature value 0.0064952756220, stated bound leaves 1.70e-8. HARD. -/
theorem leaf_q1 :
    (6495258622/1000000000000 : ℝ) ≤ ∫ t in (11/5 : ℝ)..(89/40 : ℝ), tableKernel 0 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, quarter panel `[89/40, 9/4]`
of `a_{1,2}`: quadrature value 0.0065320228138, stated bound leaves 1.70e-8. HARD. -/
theorem leaf_q2 :
    (6532005813/1000000000000 : ℝ) ≤ ∫ t in (89/40 : ℝ)..(9/4 : ℝ), tableKernel 0 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, quarter panel `[9/4, 91/40]`
of `a_{1,2}`: quadrature value 0.0065661446811, stated bound leaves 1.70e-8. HARD. -/
theorem leaf_q3 :
    (6566127681/1000000000000 : ℝ) ≤ ∫ t in (9/4 : ℝ)..(91/40 : ℝ), tableKernel 0 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, quarter panel `[91/40, 23/10]`
of `a_{1,2}`: quadrature value 0.0065976249335, stated bound leaves 1.70e-8. HARD. -/
theorem leaf_q4 :
    (6597607933/1000000000000 : ℝ) ≤ ∫ t in (91/40 : ℝ)..(23/10 : ℝ), tableKernel 0 t := by
  sorry

/-- The kernel of row 1 is interval integrable on any subinterval of `[1, 3]`. -/
theorem kernel0_integrable {a b : ℝ} (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hb1 : 1 ≤ b) (hb3 : b ≤ 3) :
    IntervalIntegrable (tableKernel 0) volume a b :=
  (Burst8P2.table_kernel_integrable 0).mono_set
    (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; left; exact ⟨ha1, ha3⟩)
      (by rw [Set.mem_uIcc]; left; exact ⟨hb1, hb3⟩))

/-- The left half panel bound of `entry_0_1` from the quarter leaves `leaf_q1` and `leaf_q2`. -/
theorem half_left :
    (1302726441/100000000000 : ℝ) ≤ ∫ t in (11/5 : ℝ)..(9/4 : ℝ), tableKernel 0 t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (kernel0_integrable (by norm_num) (by norm_num) (by norm_num) (by norm_num) :
      IntervalIntegrable (tableKernel 0) volume (11/5 : ℝ) (89/40 : ℝ))
    (kernel0_integrable (by norm_num) (by norm_num) (by norm_num) (by norm_num) :
      IntervalIntegrable (tableKernel 0) volume (89/40 : ℝ) (9/4 : ℝ))]
  have h1 := leaf_q1
  have h2 := leaf_q2
  linarith

/-- The right half panel bound of `entry_0_1` from the quarter leaves `leaf_q3` and `leaf_q4`. -/
theorem half_right :
    (13163735591/1000000000000 : ℝ) ≤ ∫ t in (9/4 : ℝ)..(23/10 : ℝ), tableKernel 0 t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (kernel0_integrable (by norm_num) (by norm_num) (by norm_num) (by norm_num) :
      IntervalIntegrable (tableKernel 0) volume (9/4 : ℝ) (91/40 : ℝ))
    (kernel0_integrable (by norm_num) (by norm_num) (by norm_num) (by norm_num) :
      IntervalIntegrable (tableKernel 0) volume (91/40 : ℝ) (23/10 : ℝ))]
  have h3 := leaf_q3
  have h4 := leaf_q4
  linarith

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_0_1_p4

#print axioms LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_0_1_p4.half_left
#print axioms LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_0_1_p4.half_right
