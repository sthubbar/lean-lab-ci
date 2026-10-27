/-
P0083, pages 488 and 489, equations 36 and 37. Arbitrary small power majorants.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.FactorBound
import LeanLab.Perelli1996.SquarefreeGrowth

namespace LeanLab.Perelli1996.Section3
open Real Polynomial

/-- Equation 36 gives a power majorant with every positive exponent loss. -/
theorem arithmeticFactor_le_rpow_of_pos (n : ℕ) (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    arithmeticFactor n ≤ (8 * (1 + 1 / δ) ^ 2) * (n : ℝ) ^ (-1 + 2 * δ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let e := (n : ℝ) ^ δ
  have he1 : 1 ≤ e := Real.one_le_rpow hn1 hδ.le
  have hlog : Real.log n ≤ e / δ := Real.log_le_rpow_div hnR.le hδ
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hplus : 1 + Real.log n ≤ (1 + 1 / δ) * e := by
    have he0 : 0 ≤ e := by positivity
    have hδ0 : δ ≠ 0 := ne_of_gt hδ
    have hnorm : (1 + 1 / δ) * e = e + e / δ := by ring
    rw [hnorm]
    linarith
  have hs := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log n) hplus 2
  have he2 : e ^ 2 = (n : ℝ) ^ (2 * δ) := by
    dsimp [e]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    congr 1
    norm_num
    ring
  have hdiv : (n : ℝ) ^ (2 * δ) / n = (n : ℝ) ^ (-1 + 2 * δ) := by
    rw [show -1 + 2 * δ = 2 * δ - 1 by ring, Real.rpow_sub hnR, Real.rpow_one]
  calc arithmeticFactor n ≤ 8 * (1 + Real.log n) ^ 2 / n := arithmeticFactor_le n hn
    _ ≤ (8 * (1 + 1 / δ) ^ 2) * (e ^ 2 / n) := by
      have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 8)) hnR.le
      convert hb using 1 <;> ring
    _ = (8 * (1 + 1 / δ) ^ 2) * (n : ℝ) ^ (-1 + 2 * δ) := by rw [he2, hdiv]

/-- The coefficient in equation 37 has every power decay exponent below two. -/
theorem weighted_roots_power_bound (F : ℤ[X]) (hF : Admissible F) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d →
      arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d ≤
        C * (d : ℝ) ^ (-2 + ε) := by
  obtain ⟨C, hC, hroot⟩ := Roots.squarefreeRootGrowth F hF (ε / 2) (by positivity)
  let δ := ε / 4
  let K : ℝ := 8 * (1 + 1 / δ) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K * C, mul_pos hK hC, fun d hd => ?_⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  by_cases hsq : Squarefree d
  · have hf := arithmeticFactor_le_rpow_of_pos d hd hδ
    change arithmeticFactor d ≤ K * (d : ℝ) ^ (-1 + 2 * δ) at hf
    have hr := hroot d hsq
    have hm := mul_le_mul hf hr (Nat.cast_nonneg (Roots.rootResidues F d).card)
      (show 0 ≤ K * (d : ℝ) ^ (-1 + 2 * δ) by positivity)
    calc arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d
        ≤ (K * (d : ℝ) ^ (-1 + 2 * δ)) * (C * (d : ℝ) ^ (ε / 2)) / d :=
          div_le_div_of_nonneg_right hm hdR.le
      _ = (K * C) * ((d : ℝ) ^ (-1 + 2 * δ) * (d : ℝ) ^ (ε / 2) / d) := by ring
      _ = (K * C) * (d : ℝ) ^ (-2 + ε) := by
        congr 1
        rw [← Real.rpow_add hdR]
        have hpow : -1 + 2 * δ + ε / 2 = (-2 + ε) + 1 := by dsimp [δ]; ring
        rw [hpow, Real.rpow_add_one hdR.ne']
        exact mul_div_cancel_right₀ _ hdR.ne'
  · rw [arithmeticFactor_nonsquarefree hsq, zero_mul, zero_div]
    positivity

end LeanLab.Perelli1996.Section3
