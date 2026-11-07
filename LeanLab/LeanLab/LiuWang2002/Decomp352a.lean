import LeanLab.LiuWang2002.ScanCert352
import LeanLab.LiuWang2002.Decomp368a

/-!
Supply split of the finite theta leaf in Decomp345c.
Schoenfeld 1976 page 356, display 5.1 star, finite range argument.
The integer certificates and their block cutoffs are derived proof data.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task352
open Real

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for the
first remaining finite block. No real logarithm computation is assumed. -/
theorem primorial_block_a (n : ℕ) (hn : 64 < n) (hn' : n ≤ 10000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact primorial_through_10000 n hn hn'

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for the
second finite block. This does not include either adjacent block. -/
theorem primorial_block_b (n : ℕ) (hn : 10000 < n) (hn' : n ≤ 1000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  exact LeanLab.LiuWang2002.Task368.primorial_block_b n hn hn'

/-- LEAF. Page 356, display 5.1 star, derived integer certificate for the
last finite block through 100000000. Smaller blocks are separate inputs. -/
theorem primorial_block_c (n : ℕ) (hn : 1000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- The finite theta leaf with exactly the original statement.
CONDITIONAL ON the two remaining integer blocks above 10000.
Source page 356, display 5.1 star. -/
theorem theta_small (X : ℝ) (hX : 0 < X) (hSmall : X ≤ 10 ^ 8) :
    Chebyshev.theta X < 1.001093 * X := by
  by_cases h2 : X < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two h2]
    positivity
  · have hn2 : 2 ≤ Nat.floor X := Nat.le_floor (show (2 : ℝ) ≤ X from le_of_not_gt h2)
    have hn8 : Nat.floor X ≤ 100000000 := Nat.floor_le_of_le (by norm_num at hSmall ⊢; exact hSmall)
    have hc : primorial (Nat.floor X) * 25 ^ Nat.floor X < 68 ^ Nat.floor X := by
      by_cases h64 : Nat.floor X ≤ 64
      · exact initial_certificate _ (Finset.mem_Icc.mpr ⟨hn2, h64⟩)
      · by_cases h4 : Nat.floor X ≤ 10000
        · exact primorial_block_a _ (by omega) h4
        · by_cases h6 : Nat.floor X ≤ 1000000
          · exact primorial_block_b _ (by omega) h6
          · exact primorial_block_c _ (by omega) hn8
    rw [Chebyshev.theta_eq_theta_coe_floor]
    exact (theta_of_primorial_certificate _ (by omega) hc).trans_le
      (mul_le_mul_of_nonneg_left (Nat.floor_le hX.le) (by norm_num))

/-- Each open certificate block has a positive integer witness.
These are derived finite range domains for page 356, display 5.1 star. -/
theorem finite_block_instances :
    (64 < (65 : ℕ) ∧ 65 ≤ 10000) ∧
    (10000 < (10001 : ℕ) ∧ 10001 ≤ 1000000) ∧
    (1000000 < (1000001 : ℕ) ∧ 1000001 ≤ 100000000) := by
  norm_num

end LeanLab.LiuWang2002.Task352

#print axioms LeanLab.LiuWang2002.Task352.theta_small
#print axioms LeanLab.LiuWang2002.Task352.finite_block_instances

#print axioms LeanLab.LiuWang2002.Task352.primorial_block_a
