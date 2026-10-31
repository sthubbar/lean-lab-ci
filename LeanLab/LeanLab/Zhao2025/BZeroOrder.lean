import LeanLab.Zhao2025.BZeroIntegral

/-!
Monotonicity for lambda0 equal to zero.
Source: Zhao 2025, display 2.19 and Lemma 2.3, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The zero lambda0 branch is nonnegative and antitone for positive lambda. -/
theorem B_zero_order (t l L : ℝ) (ht : 0 ≤ t) (hl : 0 < l) (hL : l ≤ L) :
    0 ≤ B t l 0 ∧ B t L 0 ≤ B t l 0 := by
  have hm1 := weighted_integral_antitone (fun _ => 1) 0 t l L le_rfl ht hL
    continuous_const (fun _ _ => by norm_num)
  have hm2 := weighted_integral_antitone (fun _ => 1) 0 (2 * t) l L le_rfl (by linarith) hL
    continuous_const (fun _ _ => by norm_num)
  simp only [one_mul] at hm1 hm2
  have hp2 : 0 ≤ ∫ u in 0..(2 * t), Real.exp (-l * u) :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => (Real.exp_pos _).le)
  have hpL : 0 ≤ ∫ u in 0..t, Real.exp (-L * u) :=
    intervalIntegral.integral_nonneg_of_forall ht (fun _ => (Real.exp_pos _).le)
  have hsquare := pow_le_pow_left₀ hpL hm1 2
  rw [B_zero_laplace t l (ne_of_gt hl), B_zero_laplace t L (ne_of_gt (hl.trans_le hL))]
  constructor
  · positivity
  · have := mul_le_mul_of_nonneg_left hm2 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    linarith

#print axioms B_zero_order

end LeanLab.Zhao2025.Task56
