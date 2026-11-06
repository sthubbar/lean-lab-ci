/-
P0093 page 168 equation 10.7. A comparison of candidate upper bounds.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Linnik1951

open Filter
open scoped Topology

/-- P0093 page 168 equation 10.7, comparison of candidate bounds.
A positive power upper bound does not become small after division by
the square root of a logarithm. The ratio exceeds every positive
constant eventually. This does not assert that the paper estimate fails. -/
theorem small_power_not_relative_decay439 (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C < (N : ℝ) ^ a / Real.sqrt (Real.log N) := by
  have hcp : 0 < C + 1 := by linarith
  have hh := (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ) ha).def
    (show 0 < 1 / (C + 1) by positivity)
  have hn : ∀ᶠ (N : ℕ) in atTop,
      ‖Real.log (N : ℝ) ^ (1 / 2 : ℝ)‖ ≤
        (1 / (C + 1)) * ‖(N : ℝ) ^ a‖ :=
    tendsto_natCast_atTop_atTop.eventually hh
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hn
  refine ⟨max 1 N0, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by have := le_max_left 1 N0; omega)
  have hlog : 0 < Real.log N := Real.log_pos hN1
  have hroot : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hlog
  have h := hN0 N (le_trans (le_max_right _ _) hN.le)
  rw [← Real.sqrt_eq_rpow] at h
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) a)] at h
  have hdiv : Real.sqrt (Real.log N) ≤ (N : ℝ) ^ a / (C + 1) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h
  have hm := (le_div_iff₀ hcp).mp hdiv
  apply (lt_div_iff₀ hroot).mpr
  nlinarith

end LeanLab.Linnik1951
