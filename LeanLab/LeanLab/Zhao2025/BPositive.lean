import LeanLab.Zhao2025.BNonnegOrder

/-!
Strict positivity supplies a uniform budget for the additive row error.
Source: Zhao 2025, displays 2.19 and 2.22, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6825

/-- B is strictly positive when t and lambda are positive and lambda0 is nonnegative. -/
theorem B_positive (t l l0 : ℝ) (ht : 0 < t) (hl : 0 < l) (h0 : 0 ≤ l0) :
    0 < B t l l0 := by
  have hI (a : ℝ) (ha : 0 < a) :
      0 < ∫ u in 0..(2 * t), Real.exp (-a * u) := by
    rw [exp_integral 0 (2 * t) (-a) (neg_ne_zero.mpr (ne_of_gt ha))]
    simp only [mul_zero, Real.exp_zero]
    apply div_pos_of_neg_of_neg
    · apply sub_neg.mpr
      apply Real.exp_lt_one_iff.mpr
      nlinarith [mul_pos ha ht]
    · linarith
  by_cases hz : l0 = 0
  · subst l0
    rw [B_zero_laplace t l (ne_of_gt hl)]
    have hi := hI l hl
    nlinarith [sq_nonneg (∫ u in 0..t, Real.exp (-l * u))]
  · have hp : 0 < l0 := lt_of_le_of_ne h0 (Ne.symm hz)
    rw [B_eq_laplace t l l0 hl hp]
    have h1 : 0 ≤ ∫ u in 0..t, (1 - Real.exp (-l0 * u)) * Real.exp (-l * u) := by
      apply intervalIntegral.integral_nonneg ht.le
      intro u hu
      apply mul_nonneg _ (Real.exp_pos _).le
      apply sub_nonneg.mpr
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg h0 hu.1]
    have h2 : 0 ≤ ∫ u in t..(2 * t),
        (Real.exp (-(2 * l0 * (u - t))) - Real.exp (-l0 * u)) * Real.exp (-l * u) := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro u hu
      apply mul_nonneg _ (Real.exp_pos _).le
      apply sub_nonneg.mpr
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr hu.2)]
    have hi := hI (l + l0) (by linarith)
    have hd : 0 ≤ 1 / l0 * ((∫ u in 0..t,
        (1 - Real.exp (-l0 * u)) * Real.exp (-l * u)) +
        ∫ u in t..(2 * t),
          (Real.exp (-(2 * l0 * (u - t))) - Real.exp (-l0 * u)) * Real.exp (-l * u)) :=
      mul_nonneg (by positivity) (add_nonneg h1 h2)
    unfold BLaplace
    linarith

#print axioms B_positive
end LeanLab.Zhao2025.Task56
