/-
Unit a33, burst CLOUD-burst20261120c, 2026-11-21. P0014 Helfgott, Major arcs for Goldbach's
problem, arXiv 1305.2897v4, Theorem 3.1 and Corollary 3.2 at k equal to zero, pages 9, 10 and
23 to 28.

Conditional twins of the sealed chain from the two contour leaves
`Decomp639Contour.saddle_segment_bound` and `Decomp639Contour.initial_segment_bound` up to
`SplitGaussian123.corollary_3_2_k0`. Each twin has the exact sealed statement with the first
argument `hA : DQInitialSegmentBound.HelfgottA33`, the named hypothesis for the computer check
of P0014 page 67, display A.33. The proofs copy the sealed proofs with the open leaf dependency
replaced by the twin below. The saddle leaf is fed by the axiom clean
`DQSaddleSegmentBound.saddle_segment_bound_twin`, the initial leaf by
`DQInitialSegmentBound.initial_segment_bound_twin hA`.
CONDITIONAL ON HelfgottA33 only. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottMajor.DQ6Decisions
import LeanLab.HelfgottMajor.DQSaddleSegmentBound
import LeanLab.HelfgottMajor.DQInitialSegmentBoundDecisions
import LeanLab.HelfgottMajor.Gaussian123Base

namespace LeanLab.HelfgottMajor.MainA33Chain123

open Real SplitGaussian123 Filter
open Decomp511a

/-- The named saddle bound of DQ6 holds, from the axiom clean twin. -/
theorem saddle_named_dq6 : DQ6.SaddleSegmentBoundDQ6 :=
  DQSaddleSegmentBound.saddle_segment_bound_twin

/-- The named initial bound of DQ6 holds under HelfgottA33. -/
theorem initial_named_dq6_of_A33 (hA : DQInitialSegmentBound.HelfgottA33) :
    DQ6.InitialSegmentBoundDQ6 :=
  DQInitialSegmentBound.initial_segment_bound_twin hA

/-- Twin of `Decomp511a.opposite_positive_contour_before_tail`, P0014 pages 23 to 25,
displays 3.56 and 3.59 to 3.64. CONDITIONAL ON HelfgottA33. -/
theorem opposite_positive_contour_before_tail_of_A33 (hA : DQInitialSegmentBound.HelfgottA33)
    (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) +
      (∫ x : ℝ in Set.Ioi (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        exp (-x ^ 2 / 2) * x ^ (s.re - 1)) :=
  DQ6.opposite_positive_contour_before_tail_of_named_dq6 saddle_named_dq6
    (initial_named_dq6_of_A33 hA) δ s hσ0 hσ1 ht hsign

theorem opposite_positive_contour_before_tail_of_A33_match
    (hA : DQInitialSegmentBound.HelfgottA33) :
    type_of% @Decomp511a.opposite_positive_contour_before_tail :=
  opposite_positive_contour_before_tail_of_A33 hA

/-- Twin of `Decomp511a.opposite_contour_before_tail`. CONDITIONAL ON HelfgottA33. -/
theorem opposite_contour_before_tail_of_A33 (hA : DQInitialSegmentBound.HelfgottA33)
    (δ : ℝ) (s : ℂ)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) +
      (∫ x : ℝ in Set.Ioi (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        exp (-x ^ 2 / 2) * x ^ (s.re - 1)) := by
  by_cases hp : 0 < s.re
  · exact opposite_positive_contour_before_tail_of_A33 hA δ s hp hσ1 ht hsign
  · have hs0 : s.re = 0 := le_antisymm (le_of_not_gt hp) hσ0
    rw [raw_mellin_zero_re δ s hs0, norm_zero]
    have hd : δ ≠ 0 := by intro h; simp [h] at hsign
    have htpos : 0 < |s.im| := by linarith
    have hm : 0 < min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|) := by
      apply lt_min
      · exact div_pos htpos (by positivity)
      · positivity
    have hi : 0 ≤ ∫ x : ℝ in Set.Ioi
        (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        exp (-x ^ 2 / 2) * x ^ (s.re - 1) := by
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := hm.trans hx
      positivity
    have hmain : 0 ≤ mainCoefficient s.re |s.im| δ := by
      unfold mainCoefficient
      positivity
    have hfirst : 0 ≤ firstCoefficient s.re |s.im| := by
      unfold firstCoefficient
      positivity
    exact add_nonneg (add_nonneg (mul_nonneg hmain (exp_nonneg _))
      (mul_nonneg hfirst (exp_nonneg _))) hi

theorem opposite_contour_before_tail_of_A33_match (hA : DQInitialSegmentBound.HelfgottA33) :
    type_of% @Decomp511a.opposite_contour_before_tail :=
  opposite_contour_before_tail_of_A33 hA

/-- Twin of `Decomp511a.opposite_sign_contour`, P0014 Theorem 3.1, displays 3.1 and 3.2.
CONDITIONAL ON HelfgottA33. -/
theorem opposite_sign_contour_of_A33 (hA : DQInitialSegmentBound.HelfgottA33)
    (δ : ℝ) (s : ℂ)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) +
      lastCoefficient s.re |s.im| δ *
        exp (-min ((1 / 8 : ℝ) * (s.im / (π * δ)) ^ 2)
          ((25 / 32 : ℝ) * |s.im|)) := by
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have h := opposite_contour_before_tail_of_A33 hA δ s hσ0 hσ1 ht hsign
  have htail := gaussian_tail_cutoff δ s.im s.re hd (by linarith) hσ0 (by linarith)
  linarith only [h, htail]

theorem opposite_sign_contour_of_A33_match (hA : DQInitialSegmentBound.HelfgottA33) :
    type_of% @Decomp511a.opposite_sign_contour :=
  opposite_sign_contour_of_A33 hA

/-- Twin of `Decomp511a.opposite_pair_expansion`, P0014 pages 27 and 28, displays 3.69 to
3.72 at k equal to zero. CONDITIONAL ON HelfgottA33. -/
theorem opposite_pair_expansion_of_A33 (hA : DQInitialSegmentBound.HelfgottA33)
    (δ : ℝ) (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤
      4.217 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      (1.025 * sqrt |s.im| * exp (-0.4798 * |s.im|) +
        (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|))⁻¹ *
          exp (-min ((1 / 8 : ℝ) * (s.im / (π * δ)) ^ 2)
            ((25 / 32 : ℝ) * |s.im|))) := by
  have ht : 100 ≤ |s.im| := (le_max_left _ _).trans hτ
  have htd : 4 * π ^ 2 * |δ| ≤ |s.im| := (le_max_right _ _).trans hτ
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have hre0 : 0 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hre1 : (1 - s).re ≤ 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have him : |(1 - s).im| = |s.im| := by simp
  have h1 := opposite_sign_contour_of_A33 hA δ s hσ0 hσ1 ht hsign
  have h2 := same_sign_contour δ (1 - s) hre0 hre1 (by simpa only [him] using ht)
    (by simp only [Complex.sub_im, Complex.one_im, zero_sub]; nlinarith only [hsign])
  rw [him] at h2
  have hm := mainCoefficient_le s.re |s.im| δ hσ0 hσ1 hd ht htd
  have hl := lastCoefficient_le s.re |s.im| δ hσ1 hd ht htd
  have he := two_errors_le s.re (1 - s).re |s.im| δ hσ1 hre1 ht htd
  have hmain := mul_le_mul_of_nonneg_right hm
    (exp_nonneg (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|))
  have hlast := mul_le_mul_of_nonneg_right hl
    (exp_nonneg (-min ((1 / 8 : ℝ) * (s.im / (π * δ)) ^ 2)
      ((25 / 32 : ℝ) * |s.im|)))
  linarith only [h1, h2, he, hmain, hlast]

theorem opposite_pair_expansion_of_A33_match (hA : DQInitialSegmentBound.HelfgottA33) :
    type_of% @Decomp511a.opposite_pair_expansion :=
  opposite_pair_expansion_of_A33 hA

/-- Twin of `Decomp511a.pair_expansion`. CONDITIONAL ON HelfgottA33. -/
theorem pair_expansion_of_A33 (hA : DQInitialSegmentBound.HelfgottA33)
    (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤
      4.217 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      (1.025 * sqrt |s.im| * exp (-0.4798 * |s.im|) +
        (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|))⁻¹ *
          exp (-min ((1 / 8 : ℝ) * (s.im / (π * δ)) ^ 2)
            ((25 / 32 : ℝ) * |s.im|))) := by
  have ht : 100 ≤ |s.im| := (le_max_left _ _).trans hτ
  have him0 : s.im ≠ 0 := by intro h; norm_num [h] at ht
  rcases lt_or_gt_of_ne (mul_ne_zero hδ him0) with hsign | hsign
  · exact opposite_pair_expansion_of_A33 hA δ s hσ0 hσ1 hτ hsign
  · have h := opposite_pair_expansion_of_A33 hA δ (1 - s)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simpa using hτ)
      (by simp only [Complex.sub_im, Complex.one_im, zero_sub]; nlinarith only [hsign])
    simpa only [sub_sub_cancel, Complex.sub_im, Complex.one_im, zero_sub,
      abs_neg, neg_div, neg_sq, add_comm (‖gaussianMellin δ (1 - s)‖)] using h

theorem pair_expansion_of_A33_match (hA : DQInitialSegmentBound.HelfgottA33) :
    type_of% @Decomp511a.pair_expansion :=
  pair_expansion_of_A33 hA

/-- Twin of `Decomp503a.saddle_pair_expansion`, P0014 pages 27 and 28, displays 3.69 to
3.72 at k equal to zero. CONDITIONAL ON HelfgottA33. -/
theorem saddle_pair_expansion_of_A33 (hA : DQInitialSegmentBound.HelfgottA33)
    (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0)
    (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤
      4.217 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
        Decomp503a.saddleRemainder δ s.im := by
  simpa only [Decomp503a.saddleRemainder] using
    pair_expansion_of_A33 hA δ s hδ hσ0 hσ1 hτ

theorem saddle_pair_expansion_of_A33_match (hA : DQInitialSegmentBound.HelfgottA33) :
    type_of% @Decomp503a.saddle_pair_expansion :=
  saddle_pair_expansion_of_A33 hA

/-- Twin of `Decomp503a.corollary_from_saddle_pieces`, P0014 display 3.4 on page 10 and
the conclusion on page 28. CONDITIONAL ON HelfgottA33. -/
theorem corollary_from_saddle_pieces_of_A33 (hA : DQInitialSegmentBound.HelfgottA33)
    (δ : ℝ) (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im := by
  have ht100 : 100 ≤ |s.im| := (le_max_left _ _).trans hτ
  by_cases hδ : δ = 0
  · subst δ
    exact Decomp503a.zero_shift_corollary s hσ0 hσ1 ht100
  · have hexp := Decomp503a.saddle_exponential_bound δ s.im hδ (by linarith)
    have hrem := Decomp503a.saddle_remainder_bound δ s.im hδ hτ
    have hE : 0 ≤ corEnvelope δ s.im := (exp_pos _).le.trans
      (Decomp503a.corEnvelope_domination δ s.im hδ).1
    calc
      _ ≤ 4.217 * exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
          Decomp503a.saddleRemainder δ s.im := saddle_pair_expansion_of_A33 hA δ s hδ hσ0 hσ1 hτ
      _ ≤ 4.217 * corEnvelope δ s.im + 0.0089 * corEnvelope δ s.im :=
        add_le_add (mul_le_mul_of_nonneg_left hexp (by norm_num)) hrem
      _ ≤ _ := by nlinarith only [hE]

theorem corollary_from_saddle_pieces_of_A33_match (hA : DQInitialSegmentBound.HelfgottA33) :
    type_of% @Decomp503a.corollary_from_saddle_pieces :=
  corollary_from_saddle_pieces_of_A33 hA

/-- Twin of `SplitGaussian123.corollary_3_2_k0` in Gaussian123Base, P0014 Corollary 3.2,
page 10, display 3.4 with k equal to 0 and c0 equal to 4.226. CONDITIONAL ON HelfgottA33. -/
theorem corollary_3_2_k0_of_A33 (hA : DQInitialSegmentBound.HelfgottA33)
    (δ : ℝ) (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im := by
  exact corollary_from_saddle_pieces_of_A33 hA δ s hσ0 hσ1 hτ

theorem corollary_3_2_k0_of_A33_match (hA : DQInitialSegmentBound.HelfgottA33) :
    type_of% @SplitGaussian123.corollary_3_2_k0 :=
  corollary_3_2_k0_of_A33 hA

end LeanLab.HelfgottMajor.MainA33Chain123

#print axioms LeanLab.HelfgottMajor.DQSaddleSegmentBound.saddle_segment_bound_twin
#print axioms LeanLab.HelfgottMajor.DQInitialSegmentBound.initial_segment_bound_twin
#print axioms LeanLab.HelfgottMajor.Decomp511a.opposite_positive_contour_before_tail
#print axioms LeanLab.HelfgottMajor.MainA33Chain123.opposite_positive_contour_before_tail_of_A33
#print axioms LeanLab.HelfgottMajor.MainA33Chain123.opposite_contour_before_tail_of_A33
#print axioms LeanLab.HelfgottMajor.MainA33Chain123.opposite_sign_contour_of_A33
#print axioms LeanLab.HelfgottMajor.MainA33Chain123.opposite_pair_expansion_of_A33
#print axioms LeanLab.HelfgottMajor.MainA33Chain123.pair_expansion_of_A33
#print axioms LeanLab.HelfgottMajor.MainA33Chain123.saddle_pair_expansion_of_A33
#print axioms LeanLab.HelfgottMajor.MainA33Chain123.corollary_from_saddle_pieces_of_A33
#print axioms LeanLab.HelfgottMajor.MainA33Chain123.corollary_3_2_k0_of_A33
#print axioms LeanLab.HelfgottMajor.MainA33Chain123.corollary_3_2_k0_of_A33_match
