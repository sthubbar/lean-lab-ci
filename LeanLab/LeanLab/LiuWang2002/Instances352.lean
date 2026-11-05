import LeanLab.LiuWang2002.Decomp352a
import LeanLab.LiuWang2002.Decomp352b

/-!
Nonempty domains and the proved initial real theta range.
Source Schoenfeld page 356, display 5.1 star and proof of display 9.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352
open Real

/-- The initial real finite range through 10000 is unconditional.
Derived finite part of page 356, display 5.1 star. -/
theorem theta_through_10000 (X : ℝ) (hX : 0 < X) (hUpper : X ≤ 10000) :
    Chebyshev.theta X < 1.001093 * X := by
  by_cases h2 : X < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two h2]
    positivity
  have hn2 : 2 ≤ Nat.floor X := Nat.le_floor (show (2 : ℝ) ≤ X from le_of_not_gt h2)
  have hnU : Nat.floor X ≤ 10000 := Nat.floor_le_of_le hUpper
  have hc : primorial (Nat.floor X) * 25 ^ Nat.floor X < 68 ^ Nat.floor X := by
    by_cases h64 : Nat.floor X ≤ 64
    · exact initial_certificate _ (Finset.mem_Icc.mpr ⟨hn2, h64⟩)
    · exact primorial_through_10000 _ (by omega) hnU
  rw [Chebyshev.theta_eq_theta_coe_floor]
  exact (theta_of_primorial_certificate _ (by omega) hc).trans_le
    (mul_le_mul_of_nonneg_left (Nat.floor_le hX.le) (by norm_num))

/-- The finite, early, bridge, late and table domains contain actual
points. The finite witness has positive theta. Page 356, display 5.1 star. -/
theorem regional_domains :
    (0 < (2 : ℝ) ∧ 2 ≤ (10 : ℝ)^8 ∧ 0 < Chebyshev.theta 2) ∧
    (∃ X : ℝ, 10 ^ 8 < X ∧ X < exp 18.43) ∧
    (exp (18.43 : ℝ) ≤ exp 18.43 ∧ exp (18.43 : ℝ) < exp 18.45) ∧
    (exp (18.45 : ℝ) ≤ exp 18.45 ∧ exp (18.45 : ℝ) < exp 18.7) ∧
    (exp (18.7 : ℝ) ≤ exp 18.7 ∧ 0 < exp (18.7 : ℝ)) := by
  refine ⟨⟨by norm_num, by norm_num, Chebyshev.theta_pos le_rfl⟩, ?_,
    ⟨le_rfl, exp_lt_exp.mpr (by norm_num)⟩,
    ⟨le_rfl, exp_lt_exp.mpr (by norm_num)⟩, ⟨le_rfl, exp_pos _⟩⟩
  refine ⟨((10 : ℝ)^8 + exp 18.43) / 2, ?_, ?_⟩
  all_goals linarith [gap_endpoint_bounds.1]

/-- A nonzero certified proper prime power gap at the first endpoint.
This checks that the lower correction inputs describe actual arithmetic.
Derived instance for page 356, display 9.3. -/
theorem positive_gap_instance :
    0 < Chebyshev.psi (100000000 : ℝ) - Chebyshev.theta (100000000 : ℝ) := by
  have h := gap_of_certificate 100000000 10512 1 (by norm_num) (by norm_num) gap_certificate_0
  norm_num at h
  linarith

end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.theta_through_10000
#print axioms LeanLab.LiuWang2002.Task352.regional_domains
#print axioms LeanLab.LiuWang2002.Task352.positive_gap_instance
