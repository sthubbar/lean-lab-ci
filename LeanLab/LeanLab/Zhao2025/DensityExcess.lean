import LeanLab.Zhao2025.PsiOrder

/-!
The finite excess sum in display 3.23 is nonnegative.
Source: Zhao 2025, displays 3.23, 3.25 and 3.26, pages 10 and 11.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6900

/-- The sum D over lambda at most the cutoff, using the actual psi ratio. -/
noncomputable def densityExcess {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (x L l0 : ℝ) : ℝ :=
  ∑ j ∈ (s.filter fun j => lam j ≤ L), (psiR x (lam j) l0 - psiR x L l0)

/-- Every summand of the density excess is nonnegative. -/
theorem density_excess_nonneg {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (x L l0 : ℝ)
    (hx : 0 < x) (h0 : 0 ≤ l0) : 0 ≤ densityExcess s lam x L l0 := by
  classical
  unfold densityExcess
  apply Finset.sum_nonneg
  intro j hj
  exact sub_nonneg.mpr (psiR_antitone x l0 hx h0 (Finset.mem_filter.mp hj).2)

#print axioms density_excess_nonneg
end LeanLab.Zhao2025.Task56
