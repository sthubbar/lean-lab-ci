import LeanLab.BHP1997.Decomp561d

namespace LeanLab.BHP1997.Decomp561d
open Classical

/-- A checked counterexample to the unrestricted order-domination statement. -/
theorem leaf_long_order_domination561_false :
    ¬ (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ⌊Real.log x ^ (2 * 0)⌋₊ ≤ order512 (-1) x) := by
  rintro ⟨X, hX⟩
  let x : ℝ := max X (Real.exp 2)
  have hXx : X ≤ x := by
    dsimp [x]
    exact le_max_left _ _
  have hxe : Real.exp 2 ≤ x := by
    dsimp [x]
    exact le_max_right _ _
  have hx1 : (1 : ℝ) ≤ x := by
    have hexp2 : (1 : ℝ) < Real.exp 2 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hxe
    rw [Real.log_exp] at h
    linarith
  have hlenle1 : length512 (-1) x ≤ 1 := by
    unfold length512
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hlen0 : (0 : ℝ) ≤ length512 (-1) x := by
    unfold length512
    exact Real.rpow_nonneg (le_trans zero_le_one hx1) _
  have hdelta : (0 : ℝ) ≤ 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
  have hord0 : order512 (-1) x = 0 := by
    unfold order512
    have h2 : (length512 (-1) x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^
        ((1 / 2 : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one (Real.rpow_nonneg hlen0 _) ?_ (by norm_num)
      exact Real.rpow_le_one hlen0 hlenle1 hdelta
    have h1 : (length512 (-1) x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^
        ((1 / 2 : ℝ)) / 2 < 1 := by
      linarith
    exact Nat.floor_eq_zero.mpr h1
  have hge : (1 : ℕ) ≤ ⌊Real.log x ^ (2 * 0)⌋₊ := by
    refine Nat.floor_pos.mpr ?_
    norm_num [Real.rpow_zero]
  have h := hX x hXx
  omega

end LeanLab.BHP1997.Decomp561d
