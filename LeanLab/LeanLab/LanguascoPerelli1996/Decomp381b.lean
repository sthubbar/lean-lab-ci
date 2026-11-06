import LeanLab.LanguascoPerelli1996.Decomp381a
import LeanLab.LanguascoPerelli1996.Cor2

/-!
P0071 pages 350, 351 and 359, Theorem 3 from the mean square leaf.
The same analytic leaf serves both Theorem 3 and Theorem 4.
No duplicate analytic admission is introduced here.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp381b
open Real intervalIntegral

/-- Pages 350 and 351, Theorem 3, using 24 at the reciprocal arc width.
Exactly the existing Theorem3. CONDITIONAL ON
Decomp381a.partial_remainder_mean_square alone. -/
theorem theorem3_decomposed : Theorem3 := by
  intro θ hθ hθ2 hG ε hε
  obtain ⟨B, X0, hB, hm⟩ := Decomp381a.partial_remainder_mean_square θ hθ hθ2
    (xiQ θ) (gmcxi_of_gmc hθ hG) ε hε
  refine ⟨B, max (max X0 1) (4 ^ (1 / θ)), ?_⟩
  intro X hX q inst hq a ha
  have hX1 : 1 ≤ X := (le_max_right X0 1).trans ((le_max_left _ _).trans hX)
  have hX0 : 0 < X := by linarith
  have hpow : 4 ≤ X ^ θ := by
    have hb : (4 : ℝ) ^ (1 / θ) ≤ X := (le_max_right _ _).trans hX
    have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 4 ^ (1 / θ)) hb hθ.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hθ.ne', Real.rpow_one] at hh
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqθ : (q : ℝ) ≤ X ^ θ := by linarith [Real.rpow_pos_of_pos hX0 θ]
  have hb := hm X ((le_max_left X0 1).trans ((le_max_left _ _).trans hX)) hX1 q hqθ a ha
    (2 * X) (by linarith) le_rfl
  simp only [Decomp381a.partialR_full, xiQ_eq hq1 hpow] at hb
  change (∫ t in (-(1 / ((q : ℝ) * (X ^ θ / 2))))..(1 / ((q : ℝ) * (X ^ θ / 2))),
      ‖R X t q a‖ ^ 2) ≤ B * X ^ (1 + ε) / ((q : ℝ) * (X ^ θ / 2))
  convert hb using 1 <;> ring

end LeanLab.LanguascoPerelli1996.Decomp381b

#print axioms LeanLab.LanguascoPerelli1996.Decomp381b.theorem3_decomposed
