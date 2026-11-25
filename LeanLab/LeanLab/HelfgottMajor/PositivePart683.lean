import LeanLab.HelfgottMajor.Gaussian309
import LeanLab.HelfgottMajor.Continuation457

/-!
Audit of the positive part transfer in the signed sampling split.
Source book Part IV page 434, the signed logarithmic weight before display 16.26.
The formal leaf drops the positive part in the wrong inequality direction.
At modulus one, zero shift and height two, the signed integral is negative.
The original sealed statement is unchanged.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PositivePart683
open Real MeasureTheory Set Decomp269a

/-- The signed main weight on the interval from one to two has negative integral
at modulus one and zero shift. The Gaussian Mellin transform does not vanish there. -/
theorem signed_gaussian_integral_neg :
    (∫ t in (1 : ℝ)..2,
      ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
        log (t / (2 * π))) < 0 := by
  have hc : Continuous (fun t : ℝ =>
      gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp
      (Continuation457.gaussian_mellin_differentiable 0 _ (by norm_num)).continuousAt
      (by fun_prop)
  have hlc : ContinuousOn (fun t : ℝ => log (t / (2 * π))) (Icc 1 2) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.log (by fun_prop)
    exact ne_of_gt (div_pos (by linarith [ht.1]) (by positivity))
  have hlog : ∀ t ∈ Icc (1 : ℝ) 2, log (t / (2 * π)) < 0 := by
    intro t ht
    apply Real.log_neg (div_pos (by linarith [ht.1]) (by positivity))
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * π)]
    linarith [Real.pi_gt_three, ht.2]
  have hne : gaussianMellin 0 ((1 / 2 : ℂ) + (1 : ℝ) * Complex.I) ≠ 0 := by
    rw [Gaussian309.mellin_zero_shift _ (by norm_num)]
    apply mul_ne_zero
    · apply mul_ne_zero (by norm_num)
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    · exact Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hpos : 0 < ∫ t in (1 : ℝ)..2,
      ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
        (-log (t / (2 * π))) := by
    apply intervalIntegral.integral_pos (by norm_num)
      (hc.norm.continuousOn.mul hlc.neg)
    · intro t ht
      exact mul_nonneg (norm_nonneg _) (neg_nonneg.mpr (hlog t ⟨ht.1.le, ht.2⟩).le)
    · refine ⟨1, by norm_num, ?_⟩
      exact mul_pos (norm_pos_iff.mpr hne) (neg_pos.mpr (hlog 1 (by norm_num)))
  simp_rw [mul_neg] at hpos
  rw [intervalIntegral.integral_neg] at hpos
  linarith

/-- The universal closure of the sealed positive part transfer leaf is false.
The witness is modulus one, its trivial character, zero shift and height two. -/
theorem high_half_weight_pos_part_le_false :
    ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          max (log ((q : ℝ) * t / (2 * π))) 0)) ≤
        (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π)))) := by
  intro h
  have hb := h 1 (1 : DirichletCharacter ℂ 1) 0 2 (by norm_num)
  simp only [Nat.cast_one, one_mul] at hb
  have hleft : 0 ≤ (1 / 4 : ℝ) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..2,
      ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
        max (log (t / (2 * π))) 0)) := by
    apply mul_nonneg (by norm_num)
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact mul_nonneg (norm_nonneg _) (le_max_right _ _)
  have hright : (1 / 4 : ℝ) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..2,
      ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
        log (t / (2 * π)))) < 0 :=
    mul_neg_of_pos_of_neg (by norm_num)
      (mul_neg_of_pos_of_neg (by positivity) signed_gaussian_integral_neg)
  exact (not_le_of_gt hright) (hleft.trans hb)

end LeanLab.HelfgottMajor.PositivePart683
