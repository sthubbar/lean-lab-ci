import LeanLab.LiuWang2002.Decomp352a
import LeanLab.LiuWang2002.Decomp368b

/-!
Assemble the completed finite prefix of Schoenfeld display 5.1 star, page 356.
Every integer certificate used here is already proved.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task664

/-- The four verified proper ranges cover this exact integer prefix. -/
theorem primorial_prefix_16m (n : ℕ) (hn : 1000000 < n) (hn' : n ≤ 16000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases h2 : n ≤ 2000000
  · exact Task368.primorial_c1 n hn h2
  by_cases h4 : n ≤ 4000000
  · exact Task368.primorial_c2 n (by omega) h4
  by_cases h8 : n ≤ 8000000
  · exact Task368.primorial_c3 n (by omega) h8
  exact Task368.primorial_c4 n (by omega) hn'

/-- The completed real theta prefix, with the paper's printed coefficient. -/
theorem theta_prefix_16m (X : ℝ) (hX : 0 < X) (hUpper : X ≤ 16000000) :
    Chebyshev.theta X < 1.001093 * X := by
  by_cases h2 : X < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two h2]
    positivity
  have hn2 : 2 ≤ Nat.floor X := Nat.le_floor (show (2 : ℝ) ≤ X from le_of_not_gt h2)
  have hnU : Nat.floor X ≤ 16000000 := Nat.floor_le_of_le hUpper
  have hc : primorial (Nat.floor X) * 25 ^ Nat.floor X < 68 ^ Nat.floor X := by
    by_cases h64 : Nat.floor X ≤ 64
    · exact Task352.initial_certificate _ (Finset.mem_Icc.mpr ⟨hn2, h64⟩)
    by_cases h4 : Nat.floor X ≤ 10000
    · exact Task352.primorial_block_a _ (by omega) h4
    by_cases h6 : Nat.floor X ≤ 1000000
    · exact Task352.primorial_block_b _ (by omega) h6
    exact primorial_prefix_16m _ (by omega) hnU
  rw [Chebyshev.theta_eq_theta_coe_floor]
  exact (Task352.theta_of_primorial_certificate _ (by omega) hc).trans_le
    (mul_le_mul_of_nonneg_left (Nat.floor_le hX.le) (by norm_num))

end LeanLab.LiuWang2002.Task664
#print axioms LeanLab.LiuWang2002.Task664.primorial_prefix_16m
#print axioms LeanLab.LiuWang2002.Task664.theta_prefix_16m
