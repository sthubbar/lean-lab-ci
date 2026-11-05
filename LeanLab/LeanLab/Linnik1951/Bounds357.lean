/-
P0093 page 166 equation 9.3. Comparison with a weaker global logarithmic bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Asymptotics357

namespace LeanLab.Linnik1951

/-- P0093 page 166 equation 9.3. A bound by N over log squared N cannot
supply any fixed positive power saving. This is a comparison of bounds,
not a counterexample to the paper's exceptional estimate. -/
theorem logarithmic_bound_not_power_saving357 (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * (N : ℝ) ^ (1 - δ) < (N : ℝ) / Real.log N ^ 2 := by
  obtain ⟨N0, hN0⟩ := power_saving_negligible357 (2 * C) δ (by positivity) hδ 2 1 (by norm_num)
  refine ⟨max 1 N0, ?_⟩
  intro N hN
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNN : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast h1)
  have hp : 0 < C * (N : ℝ) ^ (1 - δ) := by positivity
  have h := hN0 N hNN
  apply (lt_div_iff₀ (sq_pos_of_pos hlog)).mpr
  have hh : 0 < C * (N : ℝ) ^ (1 - δ) * Real.log N ^ 2 := by positivity
  nlinarith

end LeanLab.Linnik1951
