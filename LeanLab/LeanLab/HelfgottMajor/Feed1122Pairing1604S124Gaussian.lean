import LeanLab.HelfgottMajor.Feed1122Pairing1604
import LeanLab.HelfgottMajor.Decomp511a

/-!
Burst 2026-11-22, S124 split of `Feed1122Pairing1604.leaf_gaussian_mellin_norm_le`.

Source: P0014 Helfgott, Major arcs for Goldbach's problem, Theorem 3.1 display 3.3 and
Corollary 3.2 display 3.4 with k equal to 0, pages 9 and 10.

The parent bounds the norm of the Lean Mellin transform `gaussianMellin δ s` of
exp of minus t squared over 2 times e of delta t by the two branch envelope with constant 1.
The split follows the cases of the paper.

1. Real part 0. The Lean `mellin` is a Bochner integral, and at real part 0 the integrand has
   norm t inverse times exp of minus t squared over 2, not integrable at 0, so the Lean value
   is 0, not the analytic continuation that the paper means. MEDIUM.
2. Same sign, sgn delta equal to sgn tau or delta equal to 0: display 3.3 gives decay
   exp of minus pi over 4 times abs tau with an explicit polynomial factor, below
   exp of minus 0.1598 abs tau once abs tau is at least 100. MEDIUM.
3. Opposite sign, Gaussian regime abs tau below 3 over 2 times pi delta squared:
   display 3.4, first regime, with constant 1 in place of 4.226, for F at s alone, against
   the two branch envelope. HARD.
4. Opposite sign, exponential regime abs tau at least 3 over 2 times pi delta squared:
   display 3.4, second regime, likewise. HARD.

The mpmath screen of S124, recorded in the notes, finds the ratio of the norm to the two
branch envelope at most about 0.72 on the grid. Against the single branch of its regime
alone the ratio reaches about 1.23 at the crossover, for delta 4, sigma 1, tau minus
3 over 2 times pi delta squared, so the pieces keep the two branch envelope. AI wrote this Lean code.
Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122Pairing1604
open Real LeanLab.HelfgottMajor.SplitGaussian123

/-- LEAF: P0014 page 9, the Mellin transform convention, real part 0 boundary. MEDIUM.
At real part 0 the Mellin integrand of exp of minus t squared over 2 times e of delta t is
not integrable near 0, so the Bochner integral defining `gaussianMellin` is 0. -/
theorem leaf_gaussianMellin_re_zero (δ : ℝ) (s : ℂ) (hσ : s.re = 0) :
    gaussianMellin δ s = 0 := by
  unfold gaussianMellin mellin
  apply MeasureTheory.integral_undef
  intro hint
  have hint' : MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) •
      ((Real.exp (-t ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * t))) (Set.Ioi 0) := hint
  have h1 := hint'.mono_set (show Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi 0 from fun x hx => hx.1)
  have h2 : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Set.Ioo 0 1) := by
    refine (h1.norm.const_mul (Real.exp (1 / 2))).mono'
      ((measurable_id.pow_const (-1 : ℝ)).aestronglyMeasurable) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have he : ‖LeanLab.HelfgottArcs.e (δ * x)‖ = 1 := by
      simp [LeanLab.HelfgottArcs.e, Complex.norm_exp]
    have hc : ‖(x : ℂ) ^ (s - 1)‖ = x ^ (-1 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      congr 1
      simp [hσ]
    have hex : ‖(Real.exp (-x ^ 2 / 2) : ℂ)‖ = Real.exp (-x ^ 2 / 2) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [norm_smul, norm_mul, hc, hex, he, mul_one,
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hk : 1 ≤ Real.exp (1 / 2) * Real.exp (-x ^ 2 / 2) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have hp : 0 ≤ x ^ (-1 : ℝ) := Real.rpow_nonneg hx0.le _
    nlinarith
  have h3 := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-1 : ℝ)) one_pos).mp h2
  norm_num at h3

/-- LEAF: P0014 Theorem 3.1, display 3.3, page 9, the case sgn delta equal to sgn tau or
delta equal to 0, for 0 below sigma at most 1 and abs tau at least 100. MEDIUM.
Display 3.3 gives exp of minus pi over 4 times abs tau times an explicit factor polynomial in
abs tau, which is below exp of minus 0.1598 abs tau at this height. -/
theorem leaf_gaussianMellin_same_sign_le (δ : ℝ) (s : ℂ) (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) (hsign : 0 ≤ δ * s.im) :
    ‖gaussianMellin δ s‖ ≤ Real.exp (-0.1598 * |s.im|) := by
  have ht : 100 ≤ |s.im| := (le_max_left _ _).trans hτ
  have htpos : 0 < |s.im| := by linarith
  have hτne : s.im ≠ 0 := abs_pos.mp htpos
  -- strict same sign case, from Decomp511a.same_sign_contour
  have hstrict : ∀ d : ℝ, 4 * π ^ 2 * |d| ≤ |s.im| → 0 < d * s.im →
      ‖gaussianMellin d s‖ ≤ Real.exp (-0.1598 * |s.im|) := by
    intro d htd hds
    have h := Decomp511a.same_sign_contour d s hσ0.le hσ1 ht hds
    have hc := Decomp511a.sameCoefficient_le s.re |s.im| d hσ1 ht htd
    have hp := Decomp511a.polynomial_error_absorption |s.im| ht
    have hsq : Real.sqrt |s.im| ≤ |s.im| := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
    have he3 : 0 < Real.exp (-0.3 * |s.im|) := Real.exp_pos _
    have hp2 : 9 * Real.sqrt |s.im| * Real.exp (-0.3 * |s.im|) ≤ 0.0008 := by
      have := mul_le_mul_of_nonneg_right hsq he3.le
      nlinarith
    have hdec : Real.exp (-(π / 4) * |s.im|) ≤
        Real.exp (-0.3 * |s.im|) * Real.exp (-0.3 * |s.im|) * Real.exp (-0.1598 * |s.im|) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hπ : (3.14 : ℝ) ≤ π := by linarith [Real.pi_gt_d2]
      nlinarith
    have hE := Real.exp_pos (-0.1598 * |s.im|)
    have hA : 0 ≤ 9 * |s.im| * Real.exp (-0.3 * |s.im|) := by positivity
    have hB : 0 ≤ Real.sqrt |s.im| * Real.exp (-0.3 * |s.im|) := by positivity
    calc
      _ ≤ _ := h
      _ ≤ 9 * |s.im| * Real.sqrt |s.im| * (Real.exp (-0.3 * |s.im|) *
          Real.exp (-0.3 * |s.im|) * Real.exp (-0.1598 * |s.im|)) :=
        mul_le_mul hc hdec (Real.exp_nonneg _) (by positivity)
      _ = (9 * |s.im| * Real.exp (-0.3 * |s.im|)) *
          (Real.sqrt |s.im| * Real.exp (-0.3 * |s.im|)) * Real.exp (-0.1598 * |s.im|) := by ring
      _ ≤ 1 * 1 * Real.exp (-0.1598 * |s.im|) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        apply mul_le_mul (by linarith) (by nlinarith) hB (by norm_num)
      _ = _ := by ring
  rcases (eq_or_ne δ 0) with hδ | hδ
  · subst hδ
    -- limit along d = ε * s.im with ε tending to 0 from above
    let F : ℝ → ℝ → ℂ := fun ε t => (t : ℂ) ^ (s - 1) •
      ((Real.exp (-t ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (ε * s.im * t))
    have hnormF : ∀ ε t, ‖F ε t‖ = ‖F 0 t‖ := by
      intro ε t
      have he : ∀ x, ‖LeanLab.HelfgottArcs.e x‖ = 1 := by
        intro x; simp [LeanLab.HelfgottArcs.e, Complex.norm_exp]
      simp only [F, norm_smul, norm_mul, he]
    have hcont : Continuous (fun ε : ℝ => gaussianMellin (ε * s.im) s) := by
      have := MeasureTheory.continuous_of_dominated
        (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (F := F)
        (bound := fun t => ‖F 0 t‖)
        (fun ε => by
          simpa [F] using (Decomp511b.twisted_mellin_integrable (ε * s.im) s hσ0).aestronglyMeasurable)
        (fun ε => Filter.Eventually.of_forall (fun t => (hnormF ε t).le))
        (by simpa [F] using (Decomp511b.twisted_mellin_integrable 0 s hσ0).norm)
        (Filter.Eventually.of_forall (fun t => by
          simp only [F, LeanLab.HelfgottArcs.e]; fun_prop))
      simpa [gaussianMellin, mellin, F] using this
    have hlim : Filter.Tendsto (fun ε : ℝ => ‖gaussianMellin (ε * s.im) s‖)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖gaussianMellin 0 s‖) := by
      have h0 := ((hcont.norm).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h0
    have hc : (0 : ℝ) < 1 / (4 * π ^ 2) := by positivity
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hc] with ε hε
    apply hstrict
    · rw [abs_mul, abs_of_pos hε.1]
      have h1 : 4 * π ^ 2 * ε ≤ 1 := by
        have := hε.2
        rw [lt_div_iff₀ (by positivity)] at this
        linarith
      nlinarith
    · have : 0 < s.im * s.im := mul_self_pos.mpr hτne
      nlinarith [hε.1]
  · have hds : 0 < δ * s.im := by
      rcases hsign.lt_or_eq with h | h
      · exact h
      · exact absurd (mul_eq_zero.mp h.symm) (by tauto)
    exact hstrict δ ((le_max_right _ _).trans hτ) hds

/-- LEAF: P0014 Corollary 3.2, display 3.4 with k equal to 0, first branch, page 10,
sharpened to constant 1 for F at s alone, against the two branch envelope. HARD. Opposite
signs of delta and tau and abs tau below 3 over 2 times the square of pi delta. -/
theorem leaf_gaussianMellin_opposite_gauss_le (δ : ℝ) (s : ℂ) (hσ0 : 0 < s.re)
    (hσ1 : s.re ≤ 1) (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) (hsign : δ * s.im < 0)
    (hreg : |s.im| < 3 / 2 * (π * δ) ^ 2) :
    ‖gaussianMellin δ s‖ ≤ Real.exp (-0.1598 * |s.im|) + Real.exp (-0.1065 * (s.im / (π * |δ|)) ^ 2) := by
  sorry

/-- LEAF: P0014 Corollary 3.2, display 3.4 with k equal to 0, second branch, page 10,
sharpened to constant 1 for F at s alone, against the two branch envelope. HARD. Opposite
signs of delta and tau and abs tau at least 3 over 2 times the square of pi delta. -/
theorem leaf_gaussianMellin_opposite_exp_le (δ : ℝ) (s : ℂ) (hσ0 : 0 < s.re)
    (hσ1 : s.re ≤ 1) (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) (hsign : δ * s.im < 0)
    (hreg : 3 / 2 * (π * δ) ^ 2 ≤ |s.im|) :
    ‖gaussianMellin δ s‖ ≤ Real.exp (-0.1598 * |s.im|) + Real.exp (-0.1065 * (s.im / (π * |δ|)) ^ 2) := by
  sorry

/-- Assembled from the four LEAFs above. The statement of `leaf_gaussian_mellin_norm_le`
character for character. -/
theorem leaf_gaussian_mellin_norm_le_of_leaves (δ : ℝ) (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (hτ : max 100 (4 * π ^ 2 * |δ|) ≤ |s.im|) :
    ‖gaussianMellin δ s‖ ≤
      Real.exp (-0.1598 * |s.im|) +
        if δ = 0 then 0 else Real.exp (-0.1065 * (s.im / (π * |δ|)) ^ 2) := by
  have hif : 0 ≤ (if δ = 0 then (0 : ℝ) else Real.exp (-0.1065 * (s.im / (π * |δ|)) ^ 2)) := by
    split_ifs <;> positivity
  rcases hσ0.lt_or_eq with hpos | hzero
  · by_cases hsign : 0 ≤ δ * s.im
    · have h := leaf_gaussianMellin_same_sign_le δ s hpos hσ1 hτ hsign
      linarith
    · have hneg : δ * s.im < 0 := lt_of_not_ge hsign
      have hδ : δ ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hneg; exact lt_irrefl _ hneg
      by_cases hreg : |s.im| < 3 / 2 * (π * δ) ^ 2
      · have h := leaf_gaussianMellin_opposite_gauss_le δ s hpos hσ1 hτ hneg hreg
        rw [if_neg hδ]
        exact h
      · have h := leaf_gaussianMellin_opposite_exp_le δ s hpos hσ1 hτ hneg (not_lt.mp hreg)
        rw [if_neg hδ]
        exact h
  · rw [leaf_gaussianMellin_re_zero δ s hzero.symm, norm_zero]
    have := Real.exp_pos (-0.1598 * |s.im|)
    linarith

end LeanLab.HelfgottMajor.Feed1122Pairing1604
