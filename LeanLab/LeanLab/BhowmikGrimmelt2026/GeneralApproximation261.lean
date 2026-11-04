/-
The actual second moment with the full Poisson remainder at general eta.
Source: P0029 pages 26 and 27, displays 7.5 and 7.8.
The logarithm power is nine. The printed power five remains open.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ApproximationNine261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- A general eta estimate for the actual family, with logarithm power nine and the full tail. -/
theorem approximation_remainder261 {ϕ G : ℝ → ℝ}
    (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) - ∫ α in (0 : ℝ)..1,
          Sphi ϕ N α ^ 2 * bRhat G ((X : ℝ) ^ ϑ)
            (fun q => η * X * q / (X : ℝ) ^ ϑ) α * ee (-(N * α))‖ ^ 2 ≤
          C * ((η ^ 2 + ((X : ℝ) ^ ϑ) ^ 2 *
              (η * X / ((X : ℝ) ^ ϑ) ^ 2) ^ (-A)) ^ 2 * (X : ℝ) ^ 3 +
            (1 + ((X : ℝ) ^ ϑ) ^ 2 * (η * X / ((X : ℝ) ^ ϑ) ^ 2) ^ (-A)) ^ 2 *
              ((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * X) *
                Real.log X ^ 9 := by
  obtain ⟨C₁, hC₁, hmajor⟩ := major_family_remainder261 hϕ hG A hA
  obtain ⟨C₂, hC₂, hminor⟩ := minor_family_log9_remainder261 hϕ hG A hA
  refine ⟨2 * (256 * C₁ + C₂), by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hX1 hϑ.le
  have hRX : (X : ℝ) ^ ϑ ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = _ := Real.rpow_one _
  let E : ℝ := ((X : ℝ) ^ ϑ) ^ 2 * (η * X / ((X : ℝ) ^ ϑ) ^ 2) ^ (-A)
  let U : ℝ := (η ^ 2 + E) ^ 2 * (X : ℝ) ^ 3
  let V : ℝ := (1 + E) ^ 2 *
    ((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * X
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hmaj : (∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2) ≤
      C₁ * U * Real.log X := by
    simpa only [majorError150, U, E, mul_assoc] using
      hmajor X hX ((X : ℝ) ^ ϑ) η hR1 hη hη1 hscale
  have hmin : (∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) ≤
      C₂ * V * Real.log X ^ 9 := by
    simpa only [minorError150, V, E, mul_assoc] using
      hminor X hX ((X : ℝ) ^ ϑ) η hR1 hRX hη hη1 hscale
  have hmaj9 : (∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2) ≤
      256 * C₁ * U * Real.log X ^ 9 := by
    apply hmaj.trans
    nlinarith [mul_le_mul_of_nonneg_left (log_one_to_nine261 hX) (mul_nonneg hC₁ hU)]
  have hsum :
      (∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) - ∫ α in (0 : ℝ)..1,
          Sphi ϕ N α ^ 2 * bRhat G ((X : ℝ) ^ ϑ)
            (fun q => η * X * q / (X : ℝ) ^ ϑ) α * ee (-(N * α))‖ ^ 2) ≤
      2 * ((∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2) +
        ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) := by
    calc
      _ ≤ ∑ N ∈ Finset.Icc 1 X,
          2 * (‖majorError150 ϕ G X N ϑ η‖ ^ 2 + ‖minorError150 ϕ G X N ϑ η‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro N hN
        rw [error_split150 hG hX N ϑ hη]
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
      _ = _ := by rw [← Finset.sum_add_distrib, Finset.mul_sum]
  change _ ≤ 2 * (256 * C₁ + C₂) * (U + V) * Real.log X ^ 9
  apply hsum.trans
  have hlog : 0 ≤ Real.log (X : ℝ) ^ 9 := by
    exact pow_nonneg (Real.log_natCast_nonneg X) 9
  nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 256 * C₁) hV) hlog,
    mul_nonneg (mul_nonneg hC₂ hU) hlog]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.approximation_remainder261
