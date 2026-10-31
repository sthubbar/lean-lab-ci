import LeanLab.Pintz2021.Statements

/-!
The power of two cutoff in P0054 page 13 display 4.1.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.CutoffTask53

/-- The original natural exponent cutoff fits the logarithmic finite estimates. -/
theorem floor_Lnu_le_logb {X : ℝ} (hX : 1 ≤ X) :
    (⌊Lnu X⌋₊ : ℝ) ≤ Real.logb 2 X := by
  have hL : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX
  by_cases hn : 0 ≤ Lnu X
  · calc
      _ ≤ Lnu X := Nat.floor_le hn
      _ ≤ Real.logb 2 X := by
        unfold Lnu
        linarith [Real.sqrt_nonneg (Real.logb 2 X)]
  · have hz : ⌊Lnu X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    simpa only [hz, Nat.cast_zero] using hL

/-- The shortened cutoff retains at least half the logarithmic scale. -/
theorem Lnu_bounds {X : ℝ} (hX : 16 ≤ X) :
    Real.logb 2 X / 2 ≤ Lnu X ∧ Lnu X ≤ Real.logb 2 X := by
  have hX0 : 0 < X := by linarith
  have hL4 : 4 ≤ Real.logb 2 X :=
    (Real.le_logb_iff_rpow_le (by norm_num) hX0).mpr (by convert hX using 1 <;> norm_num)
  have hsqrt : Real.sqrt (Real.logb 2 X) ≤ Real.logb 2 X / 2 := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ Real.logb 2 X / 2)).mpr
    nlinarith
  unfold Lnu
  constructor <;> linarith [Real.sqrt_nonneg (Real.logb 2 X)]

end LeanLab.Pintz2021.CutoffTask53

#print axioms LeanLab.Pintz2021.CutoffTask53.floor_Lnu_le_logb
#print axioms LeanLab.Pintz2021.CutoffTask53.Lnu_bounds
