/-
Refutation of the statement of leaf_long_order_domination561 in
LeanLab.BHP1997.SPLIT_leaf_long_prefix_replacement561.
The statement has no positivity hypothesis on 11 / 20 + ε.
When ε ≤ -11 / 20 (for example ε = -1) and D = 0, length512 ε x ≤ 1
for all x ≥ 1, so order512 ε x = 0.
On the other hand, for x ≥ exp 2, Real.log x ^ (2 * 0) = (Real.log x) ^ 0 = 1,
so ⌊Real.log x ^ (2 * 0)⌋₊ = 1.
Thus for any candidate X, choosing x = max X (Real.exp 2) makes the conclusion
1 ≤ 0, which is false. No such X exists.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_long_prefix_replacement561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- The statement of `leaf_long_order_domination561`, quantified over all its arguments,
is false. -/
theorem leaf_long_order_domination561_false : ¬ (∀ (ε D : ℝ) (_hD : 0 ≤ D),
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x) := by
  intro h
  obtain ⟨X, hX⟩ := h (-1) 0 (le_refl 0)
  set x : ℝ := max X (Real.exp 2) with hx
  have hXx : X ≤ x := le_max_left _ _
  have hxe : Real.exp 2 ≤ x := le_max_right _ _
  have hexp2 : (1 : ℝ) < Real.exp 2 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hx1' : 1 < x := lt_of_lt_of_le hexp2 hxe
  have hx1 : (1 : ℝ) ≤ x := le_of_lt hx1'
  have hc : 11 / 20 + (-1 : ℝ) ≤ 0 := by norm_num
  have hlenle : length512 (-1) x ≤ 1 := by
    unfold length512
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1 hc
  have hlen0 : (0 : ℝ) ≤ length512 (-1) x := by
    unfold length512
    exact Real.rpow_nonneg (by linarith) _
  have hdelta : (0 : ℝ) ≤ 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
  have hord0 : order512 (-1) x = 0 := by
    unfold order512
    have h2 : (length512 (-1) x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 / 2 : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one (Real.rpow_nonneg hlen0 _) ?_ (by norm_num)
      exact Real.rpow_le_one hlen0 hlenle hdelta
    have h1 : (length512 (-1) x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 / 2 : ℝ)) / 2 < 1 := by
      linarith
    exact Nat.floor_eq_zero.mpr h1
  have hle := hX x hXx
  have hlog : Real.log x ^ (2 * (0 : ℝ)) = 1 := by
    ring_nf
    exact Real.rpow_zero (Real.log x)
  rw [hlog, Nat.floor_one, hord0] at hle
  omega

#print axioms leaf_long_order_domination561_false

end LeanLab.BHP1997.Decomp561n
