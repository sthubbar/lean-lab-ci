import Mathlib
/-!
Task685. A lab obstruction for the coarse exponent five route to the energy
estimate of Bhowmik and Grimmelt 2026, page 13 display 3.8.
For every smaller real exponent and every fixed constant, a later natural
argument defeats the attempted power comparison. This concerns the coarse
proof route. The paper estimate remains open in this folder.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Task685
open Real Filter
/-- A fixed multiple of a smaller power cannot dominate the fifth power eventually. -/
theorem coarse_power_not_absorbed (p C : ℝ) (X₀ : ℕ) (hp : p < 5) :
    ∃ X : ℕ, X₀ ≤ X ∧ C * (X : ℝ) ^ p < (X : ℝ) ^ (5 : ℝ) := by
  have ht : Tendsto (fun X : ℕ => (X : ℝ) ^ (5 - p)) atTop atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 5 - p by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨X, hX, hpow⟩ := ((eventually_ge_atTop (max X₀ 1)).and
    (ht.eventually_ge_atTop (C + 1))).exists
  have hX0 : X₀ ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  refine ⟨X, hX0, ?_⟩
  calc
    C * (X : ℝ) ^ p < (X : ℝ) ^ (5 - p) * (X : ℝ) ^ p :=
      mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hXp p)
    _ = (X : ℝ) ^ (5 : ℝ) := by rw [← Real.rpow_add hXp]; congr 1; ring

end LeanLab.ExceptionalSet.Task685
