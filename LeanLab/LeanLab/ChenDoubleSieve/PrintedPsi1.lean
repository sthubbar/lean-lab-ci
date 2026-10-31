import LeanLab.ChenDoubleSieve.I1TailNumerics
import LeanLab.ChenDoubleSieve.KCertificate

/-!
# Certified printed Psi1 lower bounds

Source: https://arxiv.org/pdf/0705.1652, page 22 and Table 1 on page 30.
A smaller simplex supplies the strict saving beyond the uniform envelope.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
namespace LeanLab.ChenDoubleSieve.Wu04PrintedPsi1
open Wu04Reduced (tableS tableSp)
open Wu04JCertificate (upperJ)
open Wu04KCertificate (lowerK)
open Wu04I1 (upperI1Tail)

/-- The exact five printed lower values. -/
def printedPsi1 : Fin 5 → ℚ := ![9405211/1000000000, 6558950/1000000000, 3536751/1000000000, 1056651/1000000000, 0]

/-- Exact algebra combining the directed integral endpoints. -/
theorem printedPsi1_certificate : ∀ i : Fin 5,
    printedPsi1 i ≤ -upperJ i + lowerK i / 2 - upperI1Tail i := by decide +kernel

/-- Actual Psi1 lower bounds, CONDITIONAL ON the defining Buchstab equations only. -/
theorem printedPsi1_bounds {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω) (i : Fin 5) :
    (printedPsi1 i : ℝ) ≤ Wu04Functional.Psi1 ω (tableS i : ℝ) (tableSp i : ℝ) := by
  have hJ := (Wu04JCertificate.J_table_bounds i).2
  have hK := (Wu04KCertificate.K_table_bounds i).1
  have hI := Wu04I1.I1_table_upper_tail hω i
  have hround : (printedPsi1 i : ℝ) ≤ -(upperJ i : ℝ) + (lowerK i : ℝ)/2 - (upperI1Tail i : ℝ) := by
    have hh : (printedPsi1 i : ℝ) ≤ ((-upperJ i + lowerK i / 2 - upperI1Tail i : ℚ) : ℝ) := by
      exact_mod_cast printedPsi1_certificate i
    push_cast at hh
    exact hh
  simp only [Wu04KCertificate.leftQ, Wu04KCertificate.rightQ, Rat.cast_sub,
    Rat.cast_one, Rat.cast_div] at hK
  unfold Wu04Functional.Psi1 Wu04Functional.J Wu04Functional.K
  linarith

/-- The entire Proposition 3 half of Table1PsiBounds is discharged.
CONDITIONAL ON IsBuchstab only. -/
theorem table1_Psi1_bounds {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω) :
    ∀ i : Fin 5, Wu04Functional.tablePsi ⟨i.val+4, by omega⟩ ≤
      Wu04Functional.Psi1 ω (Wu04Functional.grid ⟨i.val+5, by omega⟩) (Wu04Functional.tableSp i) := by
  intro i
  have hh := printedPsi1_bounds hω i
  fin_cases i <;> norm_num [printedPsi1, Wu04Functional.tablePsi, Wu04Functional.grid,
    Wu04Functional.tableSp, tableS, tableSp] at hh ⊢ <;> exact hh

end LeanLab.ChenDoubleSieve.Wu04PrintedPsi1

#print axioms LeanLab.ChenDoubleSieve.Wu04PrintedPsi1.printedPsi1_certificate
#print axioms LeanLab.ChenDoubleSieve.Wu04PrintedPsi1.printedPsi1_bounds

#print axioms LeanLab.ChenDoubleSieve.Wu04PrintedPsi1.table1_Psi1_bounds
