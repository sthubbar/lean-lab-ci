/-
AI wrote this Lean code for CODEX task128.
Concrete nonvacuity checks for the page 433 least-pair conversion
and the counting conventions of equations 4.1 and 4.2.
-/
import LeanLab.SteinStein1965.Decomp128
import LeanLab.SteinStein1965.Histogram128

namespace LeanLab.SteinStein1965

/-- Page 433 least-pair predicates have a square-bounded instance at N equal to 10. -/
theorem decomp128_pair_instance : IsLeastGoldbachPrime 10 3 ∧ 3 * 3 < 10 := by
  refine ⟨⟨by decide, Nat.prime_three, by norm_num, ?_⟩, by decide⟩
  intro r hr hlt
  omega

/-- Equations 4.1 and 4.2 give frequencies 2 and 3 for the supplied list 3, 5. -/
theorem histogram128_instance :
    (evensIn 2 10).map (nu [3, 5]) = [0, 0, 1, 1, 1] ∧
    sigma [3, 5] 0 10 = 2 ∧ sigma [3, 5] 1 10 = 3 := by
  decide +kernel

/-- Equation 4.2 admits zero frequency at zero for a nonempty even interval. -/
theorem sigma128_zero_instance : sigma [1, 3] 0 6 = 0 ∧ IsBasisFor [1, 3] 2 6 := by
  have h : sigma [1, 3] 0 6 = 0 := by decide +kernel
  exact ⟨h, (sigma_zero_iff_basis [1, 3] 6).mp h⟩

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.decomp128_pair_instance
#print axioms LeanLab.SteinStein1965.histogram128_instance
#print axioms LeanLab.SteinStein1965.sigma128_zero_instance
