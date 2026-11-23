import LeanLab.HelfgottMajor.Decomp511a

/-!
Second split of `leaf_lower_contour_estimate` of
`HelfgottMajor/SPLIT_opposite_positive_contour_before_tail.lean`, along the contour of
P0014 pages 23 to 25.  Source: https://arxiv.org/abs/1305.2897
AI wrote this Lean code.  Binary Goldbach is open.

Why a second split.  The first split, `SPLIT_leaf_lower_contour_estimate.lean`, imports
the file of its parent, so the parent can never import it back and its sorry stays
open.  This file imports only `Decomp511a`, which is what the parent file imports, so
the parent can be closed from here.

The cut.  The paper deforms the real ray into C1, the 45 degree segment of display
3.59, then C2, the limacon of display 3.30 which meets the real axis at
`R = c0 ℓ / c1`, display 3.64, then C3, the real ray beyond `R`.  The proved identity
`Decomp639Contour.contour_shift` is that deformation.  The target integrates only up to
`a = min (|τ| / ℓ) (5 / 4 * sqrt |τ|)`, and A.36, proved as
`Decomp639Contour.realEndpoint_lower`, gives `a ≤ R`.  Hence

  `∫ in Ioc 0 a = C1 + (C2 - ∫ in Ioc a R)`,

and the two summands are bounded separately:

* C1 by the proved `Decomp639Contour.initial_segment_bound`, displays 3.59 to 3.63;
* `C2 - ∫ in Ioc a R` by the single leaf below.

Faithfulness warning for a reviewer.  The leaf is display 3.56 and 3.57, the bound of
C2 by the main term, with the real segment from `a` to `R` attached.  The paper puts
that segment into C3 and bounds it by the Gaussian tail; it never bounds it by the main
term.  So the leaf is NOT a verbatim step of the paper.  It is the price of the cut at
`a` chosen by the parent split.  On the segment the integrand is of size
`x ^ (σ - 1) * exp (-x ^ 2 / 2)` and at `a = |τ| / ℓ` this is about
`exp (-(ρ / 8) * |τ|)`, while `E ρ = ρ / 8 - 5 ρ ^ 3 / 384 + ...`, so no crude bound on the
segment fits under the main term for small `ρ`: the leaf needs the cancellation on the
segment.  Numerical check, mpmath, parabolic cylinder formula for the full integral:
the ratio of the left side of the leaf to its right side stayed at most about 0.41 for
`σ = 1`, `τ = 100` and `ρ` from `0.05` to `15`, so the leaf looks true.

Degenerate values.  `δ * s.im < 0` gives `δ ≠ 0` and `s.im ≠ 0`; `100 ≤ |s.im|`; both
`a` and `R` are positive and `a ≤ R`, so `Ioc a R` may be empty only when `a = R`,
where the leaf is display 3.57 itself.  Satisfiable at `δ = -1`, `s = 1 / 2 + 100 * I`.
-/

namespace LeanLab.HelfgottMajor.Decomp511a
open Real SplitGaussian123 Filter
open scoped Topology

/-- LEAF: P0014 page 23, displays 3.56 and 3.57, the bound of the limacon C2 by the main
term, here with the real segment from `min (|τ| / ℓ) (5 / 4 * sqrt |τ|)` to the point
`c0 ℓ / c1` of display 3.64 subtracted.  HARD: a real analytic step for Codex, the
quantitative saddle estimate of Section 3.7 together with the cancellation on the real
segment; not verbatim in the paper, see the module doc. -/
theorem leaf_saddle_minus_return_segment (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖Decomp639Contour.saddleIntegral δ s -
        ∫ x : ℝ in Set.Ioc (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|))
          (Decomp639Contour.realEndpoint δ s.im),
          (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) := by
  sorry

/-- `leaf_lower_contour_estimate` from the leaf above, the proved contour deformation
`Decomp639Contour.contour_shift`, the proved endpoint comparison A.36 and the proved
initial segment bound.  Sorry free apart from the leaf. -/
theorem leaf_lower_contour_estimate_of_leaves (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖∫ x : ℝ in Set.Ioc (0 : ℝ) (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  have htpos : 0 < |s.im| := by linarith
  have hd : δ ≠ 0 := by rintro rfl; simp at hsign
  have habs : 0 < |δ| := abs_pos.mpr hd
  have hsqt : 0 < sqrt |s.im| := sqrt_pos.mpr htpos
  set a : ℝ := min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|) with ha_def
  set R : ℝ := Decomp639Contour.realEndpoint δ s.im with hR_def
  set f : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) *
      ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x)) with hf_def
  have ha : 0 < a := lt_min (div_pos htpos (by positivity)) (by positivity)
  have haR : a ≤ R := Decomp639Contour.realEndpoint_lower δ s.im hd htpos
  have hF : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    simpa only [smul_eq_mul] using
      LeanLab.HelfgottMajor.Decomp511b.twisted_mellin_integrable δ s hσ0
  have hmel : gaussianMellin δ s = ∫ x : ℝ in Set.Ioi (0 : ℝ), f x := by
    simp only [gaussianMellin, mellin, smul_eq_mul, hf_def]
  have hsplit0 : (∫ x : ℝ in Set.Ioi (0 : ℝ), f x) =
      (∫ x : ℝ in Set.Ioc (0 : ℝ) a, f x) + ∫ x : ℝ in Set.Ioi a, f x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha.le,
      MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
    · exact hF.mono_set Set.Ioc_subset_Ioi_self
    · exact hF.mono_set (Set.Ioi_subset_Ioi ha.le)
  have hsplit1 : (∫ x : ℝ in Set.Ioi a, f x) =
      (∫ x : ℝ in Set.Ioc a R, f x) + ∫ x : ℝ in Set.Ioi R, f x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi haR,
      MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
    · exact hF.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi ha.le))
    · exact hF.mono_set (Set.Ioi_subset_Ioi (ha.le.trans haR))
  have hshift := Decomp639Contour.contour_shift δ s hσ0 hσ1 ht hsign
  have hid : (∫ x : ℝ in Set.Ioc (0 : ℝ) a, f x) =
      Decomp639Contour.initialIntegral δ s +
        (Decomp639Contour.saddleIntegral δ s - ∫ x : ℝ in Set.Ioc a R, f x) := by
    have h := hmel.symm.trans hshift
    rw [hsplit0, hsplit1] at h
    linear_combination h
  have hleaf := leaf_saddle_minus_return_segment δ s hσ0 hσ1 ht hsign
  have hinit := Decomp639Contour.initial_segment_bound δ s hσ0 hσ1 ht hsign
  show ‖∫ x : ℝ in Set.Ioc (0 : ℝ) a, f x‖ ≤ _
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  linarith only [hleaf, hinit]

end LeanLab.HelfgottMajor.Decomp511a
