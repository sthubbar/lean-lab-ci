import LeanLab.Halupczok2012.Decomp532a

/-!
Why a square root error cannot supply the cube root Voronoi leaf.
Source target: Halupczok journal page 337, below display 2.2.
https://doi.org/10.5802/jtnb.839
This is an elementary obstruction to a weaker input, not a paper error.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp598Obstruction

open Filter
open scoped Topology

/-- Any constant multiple of the cube root logarithmic error is eventually
smaller than a square root error. This explains the failed hyperbola route. -/
theorem cube_root_log_lt_square_root (C X0 : ℝ) (hC : 0 ≤ C) :
    ∃ x : ℝ, X0 ≤ x ∧ Real.exp 1 ≤ x ∧
      C * x ^ (1 / 3 : ℝ) * Real.log x < x ^ (1 / 2 : ℝ) := by
  have hCp : 0 < C + 1 := by linarith
  have hb := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).bound
    (div_pos (by norm_num : (0 : ℝ) < 1) hCp)
  obtain ⟨x, hx, hX, he⟩ := (hb.and ((eventually_ge_atTop X0).and
    (eventually_ge_atTop (Real.exp 1)))).exists
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le he
  have hlog : 0 ≤ Real.log x := Real.log_nonneg
    ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans he)
  have hsmall : Real.log x ≤ (1 / (C + 1)) * x ^ (1 / 6 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog,
      abs_of_nonneg (Real.rpow_nonneg hx0.le (1 / 6))] using hx
  have hpow : x ^ (1 / 3 : ℝ) * x ^ (1 / 6 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  refine ⟨x, hX, he, ?_⟩
  calc
    _ ≤ C * x ^ (1 / 3 : ℝ) * ((1 / (C + 1)) * x ^ (1 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = (C / (C + 1)) * x ^ (1 / 2 : ℝ) := by rw [← hpow]; ring
    _ < 1 * x ^ (1 / 2 : ℝ) := by
      apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos hx0 _)
      rw [div_lt_one hCp]
      linarith
    _ = _ := one_mul _

/-- A square root error bound alone cannot imply the sealed cube root log error.
This is a negative result about the attempted input replacement on page 337. -/
theorem square_root_not_bounded_by_cube_root_log :
    ¬ ∃ C X0 : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X0 ≤ x → Real.exp 1 ≤ x →
      x ^ (1 / 2 : ℝ) ≤ C * x ^ (1 / 3 : ℝ) * Real.log x := by
  rintro ⟨C, X0, hC, hb⟩
  obtain ⟨x, hX, he, hx⟩ := cube_root_log_lt_square_root C X0 hC
  exact (hb x hX he).not_gt hx

end LeanLab.Halupczok2012.Decomp598Obstruction
