import LeanLab.LiuWang2002.Decomp460a
import LeanLab.LiuWang2002.Decomp460b
import LeanLab.LiuWang2002.Decomp460c
import LeanLab.LiuWang2002.Supply368

/-!
Real consequences and exact assemblies of the bounded integer supply.
Source Schoenfeld page 356, display 5.1 star.
The full assemblies remain CONDITIONAL ON the named open subranges.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task460

/-- The real theta bound through the checked endpoint 2311296.
Source page 356, display 5.1 star, derived finite consequence. -/
theorem theta_prefix (X : ℝ) (hX : 0 < X) (hUpper : X ≤ 2311296) :
    Chebyshev.theta X < 1.001093 * X := by
  by_cases hOld : X ≤ 2000000
  · exact Task368.theta_through_2000000 X hX hOld
  have hnU : Nat.floor X ≤ 2311296 := Nat.floor_le_of_le hUpper
  have hge : 2000000 ≤ Nat.floor X := Nat.le_floor (le_of_lt (lt_of_not_ge hOld))
  have hc : primorial (Nat.floor X) * 25 ^ Nat.floor X < 68 ^ Nat.floor X := by
    by_cases hFloor : Nat.floor X ≤ 2000000
    · exact Task368.prefix_132 _ (by omega) hFloor
    · exact range460_18 _ (by omega) hnU
  rw [Chebyshev.theta_eq_theta_coe_floor]
  exact (Task352.theta_of_primorial_certificate _ (by omega) hc).trans_le
    (mul_le_mul_of_nonneg_left (Nat.floor_le hX.le) (by norm_num))

/-- Exact final integer block. CONDITIONAL ON the named remaining
proper subranges. Source page 356, display 5.1 star. -/
theorem primorial_block_c (n : ℕ) (hn : 1000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases h1 : n ≤ 2000000
  · exact Task368.primorial_c1 n hn h1
  by_cases h2 : n ≤ 4000000
  · exact primorial_c2 n (by omega) h2
  by_cases h3 : n ≤ 8000000
  · exact primorial_c3 n (by omega) h3
  by_cases h4 : n ≤ 16000000
  · exact primorial_c4 n (by omega) h4
  by_cases h5 : n ≤ 32000000
  · exact primorial_c5 n (by omega) h5
  exact primorial_c6 n (by omega) hn'

/-- Exact finite real theta statement. CONDITIONAL ON the remaining
proper integer subranges. Source page 356, display 5.1 star. -/
theorem theta_small (X : ℝ) (hX : 0 < X) (hSmall : X ≤ 10 ^ 8) :
    Chebyshev.theta X < 1.001093 * X := by
  by_cases hOld : X ≤ 2000000
  · exact Task368.theta_through_2000000 X hX hOld
  have hn : 1000000 < Nat.floor X := by
    have hge : 2000000 ≤ Nat.floor X := Nat.le_floor (le_of_lt (lt_of_not_ge hOld))
    omega
  have hnU : Nat.floor X ≤ 100000000 :=
    Nat.floor_le_of_le (by norm_num at hSmall ⊢; exact hSmall)
  have hc := primorial_block_c (Nat.floor X) hn hnU
  rw [Chebyshev.theta_eq_theta_coe_floor]
  exact (Task352.theta_of_primorial_certificate _ (by omega) hc).trans_le
    (mul_le_mul_of_nonneg_left (Nat.floor_le hX.le) (by norm_num))

/-- The completed real prefix has a point with positive theta past
the old endpoint. Source page 356, display 5.1 star, derived instance. -/
theorem checked_prefix_instance :
    2000000 < (2000001 : ℝ) ∧ (2000001 : ℝ) ≤ 2311296 ∧
      0 < Chebyshev.theta 2000001 := by
  exact ⟨by norm_num, by norm_num, Chebyshev.theta_pos (by norm_num)⟩

end LeanLab.LiuWang2002.Task460
#print axioms LeanLab.LiuWang2002.Task460.theta_prefix
#print axioms LeanLab.LiuWang2002.Task460.primorial_block_c
#print axioms LeanLab.LiuWang2002.Task460.theta_small
#print axioms LeanLab.LiuWang2002.Task460.checked_prefix_instance
