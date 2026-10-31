import LeanLab.ChenDoubleSieve.Xi2Signs
import LeanLab.ChenDoubleSieve.PrintedPsi1
import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# Discharging the sign and functional row inputs

Source: https://arxiv.org/pdf/0705.1652, pages 14 and 15,
and page 30, equations 7.1 and 7.2.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Wu04Table
open Wu04Functional

/-- Every one of the nine Table 1 kernels is nonnegative. -/
theorem tableKernel_nonnegative (i : Fin 9) {t : ℝ} (ht : t ∈ Icc 1 3) :
    0 ≤ tableKernel i t := by
  unfold tableKernel
  split_ifs with hi
  · exact Xi2_table_nonneg ⟨i.val, hi⟩ ht
  · let j : Fin 5 := ⟨i.val-4, by omega⟩
    have hp := tableSp_admissible j
    have he : (⟨j.val+5, by omega⟩ : Fin 10) = ⟨i.val+1, by omega⟩ := by
      ext
      dsimp [j]
      omega
    rw [he] at hp
    exact Xi1_nonneg hp ht.1

/-- Only the four Psi2 numerical bounds remain in the functional row bridge.
CONDITIONAL ON Propositions 3 and 4, IsBuchstab and those four bounds. -/
theorem functional_rows {H ω : ℝ → ℝ} (hω : IsBuchstab ω)
    (h3 : Proposition3 H ω) (h4 : Proposition4 H ω)
    (hPsi2 : ∀ i : Fin 4, tablePsi ⟨i.val, by omega⟩ ≤ Psi2 ω (tableParams i)) :
    ∀ i : Fin 9, (printedBQ i : ℝ) + (∫ t in (1 : ℝ)..3, H t * tableKernel i t) ≤
      H (grid ⟨i.val+1, by omega⟩) := by
  have hfirst (j : Fin 4) : tablePsi ⟨j.val, by omega⟩ +
      (∫ t in (1 : ℝ)..3, H t * Xi2 (tableParams j) t) ≤ H (tableParams j).s :=
    (add_le_add (hPsi2 j) le_rfl).trans (h4 _ (tableParams_admissible j))
  have hlast (j : Fin 5) : tablePsi ⟨j.val+4, by omega⟩ +
      (∫ t in (1 : ℝ)..3, H t * Xi1 (grid ⟨j.val+5, by omega⟩) (tableSp j) t) ≤
      H (grid ⟨j.val+5, by omega⟩) :=
    (add_le_add (Wu04PrintedPsi1.table1_Psi1_bounds hω j) le_rfl).trans
      (h3 _ _ (tableSp_admissible j))
  intro i
  fin_cases i
  · have hh := hfirst 0
    norm_num [tableKernel, printedBQ, tablePsi, tableParams, grid, tableSp] at hh ⊢
    exact hh
  · have hh := hfirst 1
    norm_num [tableKernel, printedBQ, tablePsi, tableParams, grid, tableSp] at hh ⊢
    exact hh
  · have hh := hfirst 2
    norm_num [tableKernel, printedBQ, tablePsi, tableParams, grid, tableSp] at hh ⊢
    exact hh
  · have hh := hfirst 3
    norm_num [tableKernel, printedBQ, tablePsi, tableParams, grid, tableSp] at hh ⊢
    exact hh
  · have hh := hlast 0
    norm_num [tableKernel, printedBQ, tablePsi, tableParams, grid, tableSp] at hh ⊢
    exact hh
  · have hh := hlast 1
    norm_num [tableKernel, printedBQ, tablePsi, tableParams, grid, tableSp] at hh ⊢
    exact hh
  · have hh := hlast 2
    norm_num [tableKernel, printedBQ, tablePsi, tableParams, grid, tableSp] at hh ⊢
    exact hh
  · have hh := hlast 3
    norm_num [tableKernel, printedBQ, tablePsi, tableParams, grid, tableSp] at hh ⊢
    exact hh
  · have hh := hlast 4
    norm_num [tableKernel, printedBQ, tablePsi, tableParams, grid, tableSp] at hh ⊢
    exact hh

end LeanLab.ChenDoubleSieve.Wu04Table

#print axioms LeanLab.ChenDoubleSieve.Wu04Table.tableKernel_nonnegative
#print axioms LeanLab.ChenDoubleSieve.Wu04Table.functional_rows
