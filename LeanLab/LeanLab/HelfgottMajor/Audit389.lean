import LeanLab.HelfgottMajor.Decomp389a

/-!
Source route checks for Lemma 4.4, P0014 pages 39 and 40.
These are QUESTIONS about intermediate steps, not refutations of the sealed leaf.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Audit389
open Real MeasureTheory Set LeanLab.HelfgottArcs

/-- A compact test profile for the normalization in the first display on page 40. -/
noncomputable def csTest (t : ℝ) : ℝ := (Icc (-2 : ℝ) 2).indicator (fun _ => 1) t

/-- The page 40 normalized product cannot be a general Cauchy Schwarz inequality.
The test profile is one on the interval from minus 2 to 2 and zero elsewhere.
This does not assert that the Gaussian middle mass bound is false.
-/
theorem normalized_cs_test_failure :
    ¬ ((∫ _t in Icc (1 : ℝ) 2, (1 : ℝ)) ≤
      sqrt (1 / (2 * π) * ∫ t : ℝ, csTest t ^ 2) *
        sqrt (1 / π * ∫ _t in Icc (1 : ℝ) 2, (1 : ℝ) ^ 2)) := by
  have hf : (∫ t : ℝ, csTest t ^ 2) = 4 := by
    have heq : (fun t : ℝ => csTest t ^ 2) = (Icc (-2 : ℝ) 2).indicator (fun _ => 1) := by
      funext t
      by_cases h : t ∈ Icc (-2 : ℝ) 2 <;> simp [csTest, indicator, h]
    rw [heq, integral_indicator measurableSet_Icc]
    norm_num
  have hg : (∫ _t in Icc (1 : ℝ) 2, (1 : ℝ)) = 1 := by norm_num
  rw [hf, hg]
  norm_num only [one_pow, hg, mul_one]
  intro h
  have hp : 0 < π := pi_pos
  have hs : 0 ≤ 1 / (2 * π) * 4 := by positivity
  rw [← Real.sqrt_mul hs] at h
  have hsq := (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).mp h
  have hpi := pi_gt_three
  have hden : 0 < π ^ 2 := by positivity
  have he : 1 / (2 * π) * 4 * (1 / π) = 2 / π ^ 2 := by field_simp; ring
  rw [he] at hsq
  have := (le_div_iff₀ hden).mp hsq
  nlinarith

/-- The Gaussian after multiplication by the Fourier phase is not real valued.
This tests the reality justification after display 4.32 on page 39 at delta equal to 1.
-/
theorem gaussian_modulation_im_pos :
    0 < (((exp (-((1 / 4 : ℝ) ^ 2) / 2) : ℝ) : ℂ) * e (1 / 4)).im := by
  have he : e (1 / 4) = Complex.I := by
    unfold e
    convert Complex.exp_pi_div_two_mul_I using 1 <;> congr 1 <;> push_cast <;> ring
  rw [he]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
  exact exp_pos _

end LeanLab.HelfgottMajor.Audit389
