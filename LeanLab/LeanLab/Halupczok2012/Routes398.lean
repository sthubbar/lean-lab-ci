import LeanLab.Halupczok2012.Statements

/-!
A negative route check for Halupczok page 337, display 2.2.
The fixed residue range does not let the elementary Q squared error be absorbed into R.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Routes398

/-- In the admissible family X = R = Y = Q = t, the Q squared term exceeds any fixed multiple of R.
This checks the prime free moment leaf, whose domain permits X = Y. -/
theorem fixed_level_square_obstruction (M : ℝ) :
    ∃ t : ℝ, 1 < t ∧ t ≤ t ^ (3 / 2 : ℝ) * t ^ (-(1 / 2) : ℝ) ∧ M * t < t ^ 2 := by
  let t := max M 1 + 1
  have ht1 : 1 < t := by dsimp [t]; have := le_max_right M 1; linarith
  have htM : M < t := by dsimp [t]; have := le_max_left M 1; linarith
  have htp : 0 < t := by linarith
  refine ⟨t, ht1, ?_, ?_⟩
  · rw [← Real.rpow_add htp, show (3 / 2 : ℝ) + -(1 / 2) = 1 by norm_num, Real.rpow_one]
  · have h := mul_lt_mul_of_pos_right htM htp
    simpa only [sq] using h

end LeanLab.Halupczok2012.Routes398
