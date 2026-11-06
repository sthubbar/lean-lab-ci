/-
P0093 page 168 equation 10.7. A negative comparison for the divisor majorant route.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Asymptotics357

namespace LeanLab.Linnik1951

/-- P0093 page 168 equation 10.7, audit of a proposed majorant.
Replacing the singular factor by any fixed positive power of N does
not give a negligible relative correction after division by the
square root of log N. Every such power eventually exceeds any fixed
constant times that square root. This is a bound comparison only. -/
theorem power_exceeds_relative_log435 (C a : ℝ) (hC : 0 < C) (ha : 0 < a) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * Real.sqrt (Real.log N) < (N : ℝ) ^ a := by
  obtain ⟨Na, hbound⟩ := power_saving_negligible357 (2 * C) a (by positivity) ha 1 1 (by norm_num)
  refine ⟨max 3 Na, ?_⟩
  intro N hN
  have h3 : 3 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNa : Na < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 1 ≤ Real.log N := by
    have hNR : (3 : ℝ) < N := by exact_mod_cast h3
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.trans hNR).le
  have h := hbound N hNa
  simp only [pow_one, one_mul] at h
  have hmul : (2 * C * Real.log N) * (N : ℝ) ^ (1 - a) ≤
      (N : ℝ) ^ a * (N : ℝ) ^ (1 - a) := by
    calc
      _ = 2 * C * (N : ℝ) ^ (1 - a) * Real.log N := by ring
      _ ≤ N := h
      _ = _ := by rw [← Real.rpow_add hNp]; simp
  have h2 : 2 * C * Real.log N ≤ (N : ℝ) ^ a :=
    le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hNp (1 - a))
  have hs : Real.sqrt (Real.log N) ≤ Real.log N := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by linarith, ?_⟩
    nlinarith
  have hCLog : 0 < C * Real.log N := mul_pos hC (by linarith)
  have hsC := mul_le_mul_of_nonneg_left hs hC.le
  nlinarith

end LeanLab.Linnik1951
