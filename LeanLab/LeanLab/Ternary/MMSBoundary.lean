/-
A boundary diagnostic for P0028 section 4.3, equation 4.1 on page 10.
The paper takes Fourier transforms on all integers after smoothing.
The existing fhat truncates to the interval from 1 to N.
This example refutes that truncated translation, not the paper lemma.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS

/-- The point mass at 1 on the integers. -/
def boundaryF (n : ℤ) : ℝ := if n = 1 then 1 else 0

/-- Average of f at n + b1 - b2 over b1,b2 in the set containing 1 and 2. -/
noncomputable def boundaryG (n : ℤ) : ℝ :=
  (boundaryF n + boundaryF (n - 1) + boundaryF (n + 1) + boundaryF n) / 4

/-- Smoothing puts positive mass outside the original interval. -/
theorem boundaryG_zero : boundaryG 0 = 1 / 4 := by
  norm_num [boundaryG, boundaryF]

/-- The transform at zero loses one quarter of the mass if smoothing is truncated. -/
theorem boundary_truncated_mass :
    fhat 4 (fun n => boundaryG n) 0 = (3 / 4 : ℂ) ∧
    fhat 4 (fun n => boundaryF n) 0 = 1 := by
  norm_num [fhat, show Finset.Icc 1 4 = {1, 2, 3, 4} from by decide, boundaryG, boundaryF]

/-- At frequency zero the Bohr averaging multiplier is one, but these transforms differ. -/
theorem boundary_truncated_identity_false :
    fhat 4 (fun n => boundaryG n) 0 ≠ fhat 4 (fun n => boundaryF n) 0 := by
  rw [boundary_truncated_mass.1, boundary_truncated_mass.2]
  norm_num

end LeanLab.Ternary.MMS
