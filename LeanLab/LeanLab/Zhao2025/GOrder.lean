import LeanLab.Zhao2025.Zhao2025U6841N0
import LeanLab.Zhao2025.LaplaceOrder

/-!
The positive polynomial kernel makes G nonnegative and antitone.
Source: Zhao 2025, displays 3.21 and 3.22, page 10.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6841

/-- G is a nonnegative Laplace transform and decreases on the whole real line. -/
theorem Gz_order (a b : ℝ) (hab : a ≤ b) : 0 ≤ Gz a ∧ Gz b ≤ Gz a := by
  have hg : ∀ u ∈ Set.Icc (0 : ℝ) 2, 0 ≤ gpoly u := by
    intro u hu
    obtain ⟨hu0, hu2⟩ := hu
    rw [gpoly_factored]
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (pow_nonneg (by linarith) _)
    nlinarith [sq_nonneg u]
  have hm := weighted_integral_antitone gpoly 0 2 a b le_rfl (by norm_num) hab
    (by unfold gpoly; fun_prop) hg
  have hp : 0 ≤ Gz a := by
    unfold Gz
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (hg u hu) (Real.exp_pos _).le
  refine ⟨hp, ?_⟩
  simpa only [Gz, neg_mul, mul_comm a, mul_comm b] using hm

#print axioms Gz_order
end LeanLab.Zhao2025.Task56
