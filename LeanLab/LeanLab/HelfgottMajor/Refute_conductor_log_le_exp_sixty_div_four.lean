/-
Refutation of the sealed leaf conductor_log_le_exp_sixty_div_four in
LeanLab.HelfgottMajor.DecompF1618.
The statement lacks a bound on q against the height.
The RHS is the constant exp 60 / 4, whereas log q is unbounded as q ranges over ℕ \ {0}.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottMajor.DecompF1618

namespace LeanLab.HelfgottMajor.Decomp269c

open Real

/-- The statement of `conductor_log_le_exp_sixty_div_four`, quantified over all `q : ℕ` with `q ≠ 0`, is false. -/
theorem conductor_log_le_exp_sixty_div_four_false :
    ¬ (∀ (q : ℕ) (_ : q ≠ 0), 0.15 * log q + 3.389 ≤ exp (0.6 * (100 : ℝ)) / 4) := by
  intro h
  set C : ℝ := exp (0.6 * (100 : ℝ)) / 4
  set X : ℝ := (C - 3.389) / 0.15 + 1
  obtain ⟨q, hq⟩ := exists_nat_gt (exp X)
  have hexp_pos : 0 < exp X := exp_pos X
  have hq_pos : 0 < (q : ℝ) := lt_trans hexp_pos hq
  have hq_ne : q ≠ 0 := by
    rintro rfl
    simp at hq_pos
  have hlog : X < log (q : ℝ) := by
    have := Real.log_lt_log hexp_pos hq
    rwa [Real.log_exp] at this
  have h_ineq := h q hq_ne
  have h_strict : C < 0.15 * log (q : ℝ) + 3.389 := calc
    C = (C - 3.389) + 3.389 := by ring
    _ < 0.15 * ((C - 3.389) / 0.15 + 1) + 3.389 := by
      have hmul : 0.15 * ((C - 3.389) / 0.15 + 1) = (C - 3.389) + 0.15 := by
        rw [mul_add, mul_div_cancel₀ _ (by norm_num), mul_one]
      rw [hmul]
      linarith
    _ = 0.15 * X + 3.389 := rfl
    _ ≤ 0.15 * log (q : ℝ) + 3.389 := by
      have hXle : X ≤ log (q : ℝ) := le_of_lt hlog
      have hmulle : 0.15 * X ≤ 0.15 * log (q : ℝ) := mul_le_mul_of_nonneg_left hXle (by norm_num)
      linarith
  linarith

#print axioms conductor_log_le_exp_sixty_div_four_false

end LeanLab.HelfgottMajor.Decomp269c
