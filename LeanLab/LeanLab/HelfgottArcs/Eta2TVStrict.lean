/-
Strictness of the interior total variation comparison left open in PROGRESS.md.
Source: https://arxiv.org/abs/1205.5252v4, page 7, equation 2.6.
This is a derived comparison with the printed sum, not a new claim about the paper.
AI wrote this Lean code for CODEX task62. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Eta2TV

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real

/-- In the open interior extremum regime, four times the printed sum is strictly too small. -/
theorem four_printed26_lt_TV {ρ : ℝ} (h1 : Real.exp 2 < ρ) (h2 : ρ < 4 * Real.exp 2)
    {D : ℝ → ℝ} (hD : IsEta2rhoDeriv ρ D) :
    ENNReal.ofReal (4 * printed26 ρ) < eVariationOn D (Icc 0 2) := by
  have hr : 0 < ρ := (Real.exp_pos 2).trans h1
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hs0 : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hr
  let s := Real.sqrt ρ / Real.exp 1
  have hlo : Real.exp 1 < Real.sqrt ρ := by
    rw [Real.lt_sqrt he.le]
    rwa [← exp_two_eq]
  have hhi : Real.sqrt ρ < 2 * Real.exp 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    rw [mul_pow, ← exp_two_eq]
    norm_num
    exact h2
  have hs1 : 1 < s := by dsimp [s]; rw [lt_div_iff₀ he]; linarith
  have hs2 : s < 2 := by dsimp [s]; rw [div_lt_iff₀ he]; exact hhi
  have hs : 0 < s := by linarith
  have hlogs : Real.log ρ = 2 * (Real.log s + 1) := by
    dsimp [s]
    rw [Real.log_div hs0.ne' he.ne', Real.log_sqrt hr.le, Real.log_exp]
    ring
  have ht1 := Real.log_lt_sub_one_of_pos hs (ne_of_gt hs1)
  have ht2 := Real.log_lt_sub_one_of_pos (show 0 < s / 2 by positivity)
    (show s / 2 ≠ 1 by linarith)
  rw [Real.log_div hs.ne' (by norm_num)] at ht2
  have hb1 : Real.log ρ < 2 * s := by linarith
  have hb2 : Real.log ρ - 2 * Real.log 2 < s := by linarith
  have h4 : 4 ≤ ρ := le_trans four_le_exp_two h1.le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 2 * Real.log 2 ≤ Real.log ρ := by
    rw [← log_four_eq]
    exact Real.log_le_log (by norm_num) h4
  have hreal : 4 * printed26 ρ < 48 * s := by
    unfold printed26
    rw [Real.log_div hr.ne' (by norm_num), log_four_eq,
      abs_of_nonpos (by linarith : 4 * Real.log 2 - 4 * Real.log ρ ≤ 0),
      abs_of_pos (by linarith : 0 < Real.log ρ)]
    rcases le_total (Real.log ρ) (4 * Real.log 2) with h | h
    · rw [abs_of_nonneg (by linarith :
        0 ≤ 2 * Real.log ρ - 4 * (Real.log ρ - 2 * Real.log 2)),
        abs_of_nonpos (by linarith : Real.log ρ - 4 * Real.log 2 ≤ 0)]
      linarith
    · rw [abs_of_nonpos (by linarith :
        2 * Real.log ρ - 4 * (Real.log ρ - 2 * Real.log 2) ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ Real.log ρ - 4 * Real.log 2)]
      linarith
  rw [eta2rho_TV_mid h1.le h2.le hD,
    ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  convert hreal using 1 <;> dsimp [s] <;> ring

/-- A concrete admissible derivative in the strict regime. -/
example : ENNReal.ofReal (4 * printed26 (2 * Real.exp 2)) <
    eVariationOn (deriv (eta2rho (2 * Real.exp 2))) (Icc 0 2) := by
  apply four_printed26_lt_TV
    (by linarith [Real.exp_pos 2]) (by linarith [Real.exp_pos 2])
  apply deriv_eta2rho_isRep
  linarith [four_le_exp_two]

end LeanLab.HelfgottArcs
