import Mathlib

/-!
The height dependence in P0071 page 355 displays 12 and 13.
The negative result concerns the scalar assembly only.
It is not a counterexample to the paper's zero sum statement.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Height108

/-- Page 355 displays 12 and 13. The scalar assembly is uniform for all nonnegative
heights if the squared bound retains 1 + T. -/
theorem one_add_height_square {z : ℂ} {A B T M E FT FU : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hFT : FT ≤ M) (hFU : FU ≤ M)
    (he : ‖z‖ ^ 2 ≤ A * (FT + FU + E)) (hv : E ≤ B * T * M) :
    ‖z‖ ^ 2 ≤ A * (2 + B) * (1 + T) * M := by
  have hbase : FT + FU + E ≤ (2 + B) * (1 + T) * M := by
    nlinarith [mul_nonneg hT hM, mul_nonneg hB hM]
  calc
    ‖z‖ ^ 2 ≤ A * (FT + FU + E) := he
    _ ≤ A * ((2 + B) * (1 + T) * M) := mul_le_mul_of_nonneg_left hbase hA
    _ = A * (2 + B) * (1 + T) * M := by ring

/-- Page 355 displays 12 and 13. A constant endpoint term cannot be absorbed
into a uniform multiple of T on all heights between zero and one.
This is an obstruction for the scalar argument, not a paper counterexample. -/
theorem no_uniform_small_height_absorption :
    ¬ ∃ D : ℝ, ∀ T : ℝ, 0 < T → T < 1 → (1 : ℝ) ≤ D * T := by
  rintro ⟨D, hD⟩
  have hp : 0 < |D| + 2 := by positivity
  have hT : 1 / (|D| + 2) < (1 : ℝ) := by
    apply (div_lt_iff₀ hp).mpr
    linarith [abs_nonneg D]
  have hh := hD (1 / (|D| + 2)) (one_div_pos.mpr hp) hT
  rw [mul_one_div] at hh
  have hbad := (le_div_iff₀ hp).mp hh
  linarith [le_abs_self D]

end LeanLab.LanguascoPerelli1996.Height108
