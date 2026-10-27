/-
AI wrote this Lean code for CODEX task70.
Section 3, page 428, and the anomalous density discussed in Section 5, pages 432 and 433.
These small computations test a proposed monotonicity shortcut, not a verification range.
-/
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.SteinStein1965

theorem primeA_seven_subset_three (n : ℕ) (h : primeA 7 n = true) : primeA 3 n = true := by
  rw [primeA_iff] at h ⊢
  exact ⟨by omega, h.2⟩

theorem primeLength3_600 : (sPrime 3 600).1.length = 43 := by decide +kernel

theorem primeLength7_600 : (sPrime 7 600).1.length = 45 := by decide +kernel

theorem cutoff_can_increase_basis_count : (sPrime 3 600).1.length < (sPrime 7 600).1.length := by
  rw [primeLength3_600, primeLength7_600]
  decide

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.primeA_seven_subset_three
#print axioms LeanLab.SteinStein1965.primeLength3_600
#print axioms LeanLab.SteinStein1965.primeLength7_600
#print axioms LeanLab.SteinStein1965.cutoff_can_increase_basis_count
