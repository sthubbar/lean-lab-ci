import LeanLab.ChenDoubleSieve.I1Numerics
import LeanLab.ChenDoubleSieve.KCertificate

/-!
# Certified lower variants for Psi1

Source: https://arxiv.org/pdf/0705.1652, page 22 and Table 1 on page 30.
These new bounds retain a uniform Buchstab envelope. They do not replace Table 1.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
namespace LeanLab.ChenDoubleSieve.Wu04Psi1
open Wu04Reduced (tableS tableSp)
open Wu04JCertificate (upperJ)
open Wu04KCertificate (lowerK)
open Wu04I1 (upperI1)

/-- Conservative new lower variants, separate from the printed values. -/
def lowerPsi : Fin 5 → ℚ := ![9405/1000000, 6558/1000000, 3536/1000000, 1056/1000000, 0]

/-- Exact algebra combining the directed integral endpoints. -/
theorem lowerPsi_certificate : ∀ i : Fin 5,
    lowerPsi i ≤ -upperJ i + lowerK i / 2 - upperI1 i := by decide +kernel

/-- Actual Psi1 lower bounds, CONDITIONAL ON the defining Buchstab equations only. -/
theorem Psi1_table_lower {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω) (i : Fin 5) :
    (lowerPsi i : ℝ) ≤ Wu04Functional.Psi1 ω (tableS i : ℝ) (tableSp i : ℝ) := by
  have hJ := (Wu04JCertificate.J_table_bounds i).2
  have hK := (Wu04KCertificate.K_table_bounds i).1
  have hI := Wu04I1.I1_table_upper hω i
  have hround : (lowerPsi i : ℝ) ≤ -(upperJ i : ℝ) + (lowerK i : ℝ)/2 - (upperI1 i : ℝ) := by
    have hh : (lowerPsi i : ℝ) ≤ ((-upperJ i + lowerK i / 2 - upperI1 i : ℚ) : ℝ) := by
      exact_mod_cast lowerPsi_certificate i
    push_cast at hh
    exact hh
  simp only [Wu04KCertificate.leftQ, Wu04KCertificate.rightQ, Rat.cast_sub,
    Rat.cast_one, Rat.cast_div] at hK
  unfold Wu04Functional.Psi1 Wu04Functional.J Wu04Functional.K
  linarith

end LeanLab.ChenDoubleSieve.Wu04Psi1

#print axioms LeanLab.ChenDoubleSieve.Wu04Psi1.lowerPsi_certificate
#print axioms LeanLab.ChenDoubleSieve.Wu04Psi1.Psi1_table_lower
