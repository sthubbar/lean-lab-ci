import LeanLab.LiuWang2002.Decomp368a
import LeanLab.LiuWang2002.Decomp368b

/-!
Real theta consequences of the integer supply for Decomp352a.
Source Schoenfeld page 356, display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368

/-- The real theta estimate through 2000000, using only checked integer
certificates. Derived finite part of page 356, display 5.1 star. -/
theorem theta_through_2000000 (X : ℝ) (hX : 0 < X) (hUpper : X ≤ 2000000) :
    Chebyshev.theta X < 1.001093 * X := by
  by_cases h2 : X < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two h2]
    positivity
  have hn2 : 2 ≤ Nat.floor X := Nat.le_floor (show (2 : ℝ) ≤ X from le_of_not_gt h2)
  have hnU : Nat.floor X ≤ 2000000 := Nat.floor_le_of_le hUpper
  have hc : primorial (Nat.floor X) * 25 ^ Nat.floor X < 68 ^ Nat.floor X := by
    by_cases h64 : Nat.floor X ≤ 64
    · exact Task352.initial_certificate _ (Finset.mem_Icc.mpr ⟨hn2, h64⟩)
    · exact prefix_132 _ (by omega) hnU
  rw [Chebyshev.theta_eq_theta_coe_floor]
  exact (Task352.theta_of_primorial_certificate _ (by omega) hc).trans_le
    (mul_le_mul_of_nonneg_left (Nat.floor_le hX.le) (by norm_num))

/-- The exact finite real theta statement from Decomp352a.
CONDITIONAL ON the five proper integer subranges above 2000000.
Source page 356, display 5.1 star. -/
theorem theta_small (X : ℝ) (hX : 0 < X) (hSmall : X ≤ 10 ^ 8) :
    Chebyshev.theta X < 1.001093 * X := by
  by_cases hU : X ≤ 2000000
  · exact theta_through_2000000 X hX hU
  have hn : 1000000 < Nat.floor X := by
    have hh : (2000000 : ℝ) ≤ X := (lt_of_not_ge hU).le
    have hi : 2000000 ≤ Nat.floor X := Nat.le_floor hh
    omega
  have hn8 : Nat.floor X ≤ 100000000 :=
    Nat.floor_le_of_le (by norm_num at hSmall ⊢; exact hSmall)
  have hc := primorial_block_c _ hn hn8
  rw [Chebyshev.theta_eq_theta_coe_floor]
  exact (Task352.theta_of_primorial_certificate _ (by omega) hc).trans_le
    (mul_le_mul_of_nonneg_left (Nat.floor_le hX.le) (by norm_num))

/-- The new real prefix includes a point with positive theta beyond
the old prefix. Derived instance for page 356, display 5.1 star. -/
theorem prefix_domain_instance :
    10000 < (10001 : ℝ) ∧ (10001 : ℝ) ≤ 2000000 ∧ 0 < Chebyshev.theta 10001 := by
  exact ⟨by norm_num, by norm_num, Chebyshev.theta_pos (by norm_num)⟩

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.theta_through_2000000
#print axioms LeanLab.LiuWang2002.Task368.theta_small
#print axioms LeanLab.LiuWang2002.Task368.prefix_domain_instance
