import LeanLab.GoldbachAverage.WeightedIncrement124

/-!
The pointwise square estimate for I2 after P0051 page 10 eq. 55.
Source: arXiv 2110.14250v2 page 11, first display.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.WeightedSquare124
open MeasureTheory
open FloorVariance82 WeightedIncrement124

/-- LEAF. P0051 page 11 first display, before integration, with explicit constant three. -/
theorem weighted_increment_square (N : ℕ) (hN : 1 ≤ N) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h) :
    weightedIncrement N x h ^ 2 ≤ 3 *
      ((psiFloorError (x + h) - psiFloorError x) ^ 2 * Real.exp (-2 * x / N) +
        (h / N) ^ 2 * psiFloorError (x + h) ^ 2 * Real.exp (-2 * x / N) +
        (1 / (N : ℝ)) ^ 2 *
          (∫ u in x..(x + h), |psiFloorError u| * Real.exp (-u / N)) ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let A : ℝ := (psiFloorError (x + h) - psiFloorError x) * Real.exp (-x / N)
  let a : ℝ := |psiFloorError (x + h) - psiFloorError x| * Real.exp (-x / N)
  let b : ℝ := h / N * |psiFloorError (x + h)| * Real.exp (-x / N)
  let c : ℝ := 1 / (N : ℝ) *
    ∫ u in x..(x + h), |psiFloorError u| * Real.exp (-u / N)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  have hAa : |A| = a := by
    simp only [A, a, abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : |weightedIncrement N x h - A| ≤ b + c :=
    weighted_increment_error N hN hx hh
  have hw : |weightedIncrement N x h| ≤ a + b + c := by
    calc |weightedIncrement N x h| = |(weightedIncrement N x h - A) + A| := by congr 1; ring
      _ ≤ |weightedIncrement N x h - A| + |A| := abs_add_le _ _
      _ ≤ b + c + a := by rw [hAa]; linarith
      _ = _ := by ring
  have hs := pow_le_pow_left₀ (abs_nonneg (weightedIncrement N x h)) hw 2
  rw [sq_abs] at hs
  have h3 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have hexp : Real.exp (-x / (N : ℝ)) ^ 2 = Real.exp (-2 * x / N) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  refine hs.trans (h3.trans_eq ?_)
  dsimp [a, b, c]
  simp only [mul_pow, sq_abs, hexp]

end LeanLab.GoldbachAverage.WeightedSquare124
