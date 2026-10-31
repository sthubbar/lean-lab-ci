import LeanLab.Zhao2025.BZeroScaledIntegral

/-!
The scaled zero lambda0 branch is monotone.
Source: Zhao 2025, display 2.19 and the proof of Lemma 2.3, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The zero lambda0 branch becomes monotone after exponential scaling. -/
theorem B_zero_scaled_order (t l L : ℝ) (ht : 0 ≤ t) (hl : 0 < l) (hL : l ≤ L) :
    Real.exp (l * t) * B t l 0 ≤ Real.exp (L * t) * B t L 0 := by
  have hmono (b : ℝ) (hb : 0 ≤ b) :
      (∫ u in 0..b, Real.exp (l * u) + Real.exp (-l * u)) ≤
        ∫ u in 0..b, Real.exp (L * u) + Real.exp (-L * u) := by
    apply intervalIntegral.integral_mono_on hb
      ((by fun_prop : Continuous _).intervalIntegrable 0 b)
      ((by fun_prop : Continuous _).intervalIntegrable 0 b)
    intro u hu
    simpa using exp_pair_monotone l L 0 u hl.le le_rfl hL hu.1
  have hp : 0 ≤ ∫ u in 0..(t / 2), Real.exp (l * u) + Real.exp (-l * u) :=
    intervalIntegral.integral_nonneg_of_forall (by linarith)
      (fun _ => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  rw [B_zero_scaled_eq t l (ne_of_gt hl), B_zero_scaled_eq t L (ne_of_gt (hl.trans_le hL))]
  exact add_le_add (mul_le_mul_of_nonneg_left (hmono t ht) (by norm_num))
    (pow_le_pow_left₀ hp (hmono (t / 2) (by linarith)) 2)

#print axioms B_zero_scaled_order

end LeanLab.Zhao2025.Task56
