import LeanLab.ChenDoubleSieve.Decomp350j

/-!
Finite sharp Buchstab strip certificate from Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 9 Lemma 2.10 and page 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
open scoped unitInterval
namespace LeanLab.ChenDoubleSieve.Task350
open Wu04Functional Wu04Buchstab Wu04Integral

/-- The first polynomial numerator bounds the actual delay equation solution.
Source: page 9 Lemma 2.10, derived finite method of steps enclosure. -/
theorem tailNumerator_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Icc (3 : ℝ) 4) : u * ω u ≤ tailNumerator u := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Icc 3 u) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 3 u) := by
    rw [uIcc_of_le hu.1]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have he := integral_eq_sub_of_hasDerivAt_of_le hu.1 hc
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have h3 := formula_two_three hω (u := 3) (by norm_num)
  have hinit : 3 * ω 3 ≤ (tailInitial : ℝ) := by
    norm_num only [show (3 - 1 : ℝ) = 2 by norm_num] at h3
    linarith [tailConstants_upper.2]
  have hr : Continuous tailDerivativePoly := by unfold tailDerivativePoly tailLogPoly tailReciprocal; fun_prop
  have hi : (∫ t in (3 : ℝ)..u, ω (t - 1)) ≤ ∫ t in (3 : ℝ)..u, tailDerivativePoly t := by
    apply integral_mono_on hu.1 hci.intervalIntegrable (hr.intervalIntegrable 3 u)
    intro t ht
    have htfull : t ∈ Icc (3 : ℝ) 4 := ⟨ht.1, ht.2.trans hu.2⟩
    have hl := tailLogPoly_upper htfull
    have hinv := tailReciprocal_upper htfull
    have hl0 : 0 ≤ log (t - 2) := log_nonneg (by linarith [ht.1])
    have hLP0 : 0 ≤ tailLogPoly t := hl0.trans hl
    rw [formula_two_three hω ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩]
    have heq : t - 1 - 1 = t - 2 := by ring
    rw [heq]
    unfold tailDerivativePoly
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith : 1 + log (t - 2) ≤ 1 + tailLogPoly t) hinv
      (one_div_nonneg.mpr (by linarith [ht.1])) (by linarith)
  rw [tailNumerator_integral] at hi
  linarith

/-- The second polynomial bounds omega on the shifted integration strip.
Source: page 9 Lemma 2.10, derived finite method of steps enclosure. -/
theorem tailOmegaPoly_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Icc (3 : ℝ) (7 / 2)) : ω u ≤ tailOmegaPoly u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hfull : u ∈ Icc (3 : ℝ) 4 := ⟨hu.1, by linarith [hu.2]⟩
  have hn := tailNumerator_upper hω hfull
  have hn0 := tailNumerator_nonneg hfull
  have h1 : ω u ≤ tailNumerator u / u := by rw [le_div_iff₀ hu0]; nlinarith
  have h2 := mul_le_mul_of_nonneg_left (tailReciprocalV_upper hu) hn0
  unfold tailOmegaPoly
  rw [mul_one_div] at h2
  exact h1.trans h2

/-- The final polynomial budget bounds u times the actual Buchstab solution.
Source: page 9 Lemma 2.10, derived finite method of steps enclosure. -/
theorem tailBudget_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Icc (4 : ℝ) (9 / 2)) : u * ω u ≤ tailBudget u := by
  have hc : ContinuousOn (fun t : ℝ => t * ω t) (Icc 4 u) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 4 u) := by
    rw [uIcc_of_le hu.1]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have he := integral_eq_sub_of_hasDerivAt_of_le hu.1 hc
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have hpoly : Continuous (fun t => tailOmegaPoly (t - 1)) := by
    unfold tailOmegaPoly tailNumerator tailPrimitive tailReciprocalV
    fun_prop
  have hi : (∫ t in (4 : ℝ)..u, ω (t - 1)) ≤ ∫ t in (4 : ℝ)..u, tailOmegaPoly (t - 1) := by
    apply integral_mono_on hu.1 hci.intervalIntegrable (hpoly.intervalIntegrable 4 u)
    intro t ht
    exact tailOmegaPoly_upper hω ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩
  have hOmega : Continuous tailOmegaPoly := by
    unfold tailOmegaPoly tailNumerator tailPrimitive tailReciprocalV
    fun_prop
  have heval : (∫ t in (4 : ℝ)..u, tailOmegaPoly (t - 1)) =
      tailOmegaPrimitive (u - 1) - tailOmegaPrimitive 3 := by
    rw [integral_comp_sub_right (fun v : ℝ => tailOmegaPoly v) 1]
    norm_num only [show (4 - 1 : ℝ) = 3 by norm_num]
    exact integral_eq_sub_of_hasDerivAt (fun t ht => tailOmegaPrimitive_deriv t)
      (hOmega.intervalIntegrable 3 (u - 1))
  rw [heval] at hi
  have h4 := tailNumerator_upper hω (u := 4) (by norm_num)
  unfold tailBudget
  linarith

/-- The remaining compact sharp Buchstab bound has no OPEN input.
Source: page 9 Lemma 2.10 and page 42 numerical computation. -/
theorem buchstab_four_to_four_half_clean {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ∀ u ∈ Icc (4 : ℝ) (9 / 2), ω u ≤ 280761 / 500000 := by
  intro u hu
  have hn := (tailBudget_upper hω hu).trans (tailBudget_le hu)
  apply (mul_le_mul_iff_right₀ (by linarith [hu.1] : 0 < u)).mp
  simpa only [mul_comm] using hn

end LeanLab.ChenDoubleSieve.Task350
