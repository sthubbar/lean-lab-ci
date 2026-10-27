import LeanLab.ChenDoubleSieve.I1Reduction
import LeanLab.ChenDoubleSieve.ReducedCertificate

/-!
# Rigorous uniform I1 bounds for the five Proposition 3 rows

Source: https://arxiv.org/pdf/0705.1652, page 22 and page 30, Table 1 rows 5 to 9.
These use the proved Buchstab bound and the proved Fubini reduction.
They do not by themselves certify the printed Psi1 values.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Wu04I1
open Wu04Reduced (tableS tableSp volumeHi)

/-- Every row is in the range of the uniform Buchstab comparison. -/
theorem numerical_parameters : ∀ i : Fin 5,
    (5 / 2 : ℚ) ≤ tableS i ∧ 0 < tableSp i ∧ tableS i ≤ tableSp i := by
  decide +kernel

/-- Exact rational upper bounds, rounded upwards at scale one trillion. -/
def upperI1 : Fin 5 → ℚ :=
  ![9460742470/1000000000000, 4577081917/1000000000000,
    1586604293/1000000000000, 248973386/1000000000000, 0]

/-- The final rounding certificate is exact. -/
theorem upperI1_certificate : ∀ i : Fin 5,
    (567144 / 1000000 : ℚ) * volumeHi i ≤ upperI1 i := by
  decide +kernel

/-- Uniform I1 upper bounds for every one of the five printed parameter pairs.
CONDITIONAL ON the defining IsBuchstab equations only. -/
theorem I1_table_upper {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω) (i : Fin 5) :
    Wu04Functional.I1 ω (tableS i : ℝ) (tableSp i : ℝ) ≤ (upperI1 i : ℝ) := by
  have hs : (5 / 2 : ℝ) ≤ tableS i := by
    have hh : ((5 / 2 : ℚ) : ℝ) ≤ (tableS i : ℝ) := by exact_mod_cast (numerical_parameters i).1
    push_cast at hh
    exact hh
  have hsp : (0 : ℝ) < tableSp i := by exact_mod_cast (numerical_parameters i).2.1
  have hssp : (tableS i : ℝ) ≤ tableSp i := by exact_mod_cast (numerical_parameters i).2.2
  have hs0 : (0 : ℝ) < tableS i := by linarith
  have hI := I1_le_reduced hω hs hsp (reciprocal_reduction hs0 hssp)
  have hv := (Wu04Reduced.reducedTable_bounds i).2
  have hc : (0 : ℝ) ≤ Wu04Buchstab.C := by norm_num [Wu04Buchstab.C]
  have hround : Wu04Buchstab.C * (volumeHi i : ℝ) ≤ (upperI1 i : ℝ) := by
    unfold Wu04Buchstab.C
    have hh : (((567144 / 1000000 : ℚ) * volumeHi i : ℚ) : ℝ) ≤ (upperI1 i : ℝ) := by
      exact_mod_cast upperI1_certificate i
    push_cast at hh
    exact hh
  exact hI.trans ((mul_le_mul_of_nonneg_left hv hc).trans hround)

end LeanLab.ChenDoubleSieve.Wu04I1

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.numerical_parameters
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.upperI1_certificate
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_table_upper
