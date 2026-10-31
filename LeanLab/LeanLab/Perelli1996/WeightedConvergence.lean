/-
P0083, page 489, equation 37. Absolute convergence of the divisor coefficient series.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.SquarefreeGrowth
import LeanLab.Perelli1996.FactorBound

namespace LeanLab.Perelli1996.Section3
open Finset Real Polynomial

/-- A convenient power majorant for the explicit bound in equation 36. -/
theorem arithmeticFactor_le_rpow (n : ℕ) (hn : 1 ≤ n) :
    arithmeticFactor n ≤ 648 * (n : ℝ) ^ (-3 / 4 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let e := (n : ℝ) ^ (1 / 8 : ℝ)
  have he1 : 1 ≤ e := Real.one_le_rpow hn1 (by norm_num)
  have hlog : Real.log n ≤ 8 * e := by
    have h := Real.log_le_rpow_div hnR.le (by norm_num : (0 : ℝ) < 1 / 8)
    dsimp [e]
    linarith
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hsquare : (1 + Real.log n) ^ 2 ≤ 81 * e ^ 2 := by nlinarith
  have heq : e ^ 2 = (n : ℝ) ^ (1 / 4 : ℝ) := by
    dsimp [e]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
  have hdiv : (n : ℝ) ^ (1 / 4 : ℝ) / n = (n : ℝ) ^ (-3 / 4 : ℝ) := by
    have h := Real.rpow_sub hnR (1 / 4) 1
    norm_num at h
    simpa only [neg_div] using h.symm
  calc arithmeticFactor n ≤ 8 * (1 + Real.log n) ^ 2 / n := arithmeticFactor_le n hn
    _ ≤ 648 * e ^ 2 / n := by
      apply div_le_div_of_nonneg_right _ hnR.le
      nlinarith
    _ = 648 * (n : ℝ) ^ (-3 / 4 : ℝ) := by rw [heq, mul_div_assoc, hdiv]

/-- The coefficient series in equation 37 is summable for every admissible F. -/
theorem summable_weighted_roots (F : ℤ[X]) (hF : Admissible F) :
    Summable (fun d : ℕ => arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d) := by
  obtain ⟨C, hC, hroot⟩ := Roots.squarefreeRootGrowth F hF (1 / 4) (by norm_num)
  have hs : Summable (fun d : ℕ => (648 * C) * (d : ℝ) ^ (-3 / 2 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1)).mul_left (648 * C)
  apply Summable.of_nonneg_of_le
    (fun d => div_nonneg (mul_nonneg (arithmeticFactor_nonneg d) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (hf := hs)
  intro d
  by_cases hd0 : d = 0
  · subst d; simp
  by_cases hd : Squarefree d
  · have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have h1 := arithmeticFactor_le_rpow d (by omega)
    have h2 := hroot d hd
    have hmul := mul_le_mul h1 h2 (Nat.cast_nonneg (Roots.rootResidues F d).card)
      (show 0 ≤ 648 * (d : ℝ) ^ (-3 / 4 : ℝ) by positivity)
    have hdiv := div_le_div_of_nonneg_right hmul hdR.le
    calc arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d
        ≤ (648 * (d : ℝ) ^ (-3 / 4 : ℝ)) * (C * (d : ℝ) ^ (1 / 4 : ℝ)) / d := hdiv
      _ = (648 * C) * ((d : ℝ) ^ (-3 / 4 : ℝ) * (d : ℝ) ^ (1 / 4 : ℝ) / d) := by ring
      _ = (648 * C) * (d : ℝ) ^ (-3 / 2 : ℝ) := by
        congr 1
        rw [← Real.rpow_add hdR]
        have h := Real.rpow_sub hdR ((-3 / 4 : ℝ) + 1 / 4) 1
        norm_num at h ⊢
        simpa only [neg_div] using h.symm
  · rw [arithmeticFactor_nonsquarefree hd, zero_mul, zero_div]
    positivity

end LeanLab.Perelli1996.Section3
