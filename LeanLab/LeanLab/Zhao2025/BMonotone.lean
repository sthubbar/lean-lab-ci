import LeanLab.Zhao2025.Zhao2025U6825Lemma31

/-!
Elementary integral tools for the monotonicity input in Lemma 2.3.
Source: Zhao 2025, displays 2.15 and 2.22, pages 5 and 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- An elementary antiderivative used to verify the Laplace representation. -/
theorem exp_integral (a b c : ℝ) (hc : c ≠ 0) :
    ∫ u in a..b, Real.exp (c * u) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  have hd (u : ℝ) : HasDerivAt (fun v => Real.exp (c * v) / c) (Real.exp (c * u)) u := by
    convert (((hasDerivAt_id u).const_mul c).exp.div_const c) using 1 <;> simp [hc]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)]
  · ring
  · exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (c * u))).intervalIntegrable a b

#print axioms exp_integral

end LeanLab.Zhao2025.Task56
