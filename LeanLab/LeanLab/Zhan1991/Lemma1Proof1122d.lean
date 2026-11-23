/-
P0068 Zhan 1991, Lemma 1, page 261, the first derivative test cited from Titchmarsh Lemma 4.3.
Proof of the Prop `Lemma1` of SPLIT_theorem2_1122.lean with constant `K = 1`, through the second
mean value theorem of Bonnet as stated in Mathlib, `MeanValue.lean`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Real Set MeasureTheory intervalIntegral Complex

noncomputable section

/-- Second mean value step: a monotone weight bounded by `C`, against `h` whose tail integrals
are bounded by `B`. -/
theorem lemma1_smvt_bound (a b C B : ℝ) (g : ℝ → ℝ) (h : ℝ → ℂ) (hab : a ≤ b)
    (hg : MonotoneOn g (Icc a b)) (hgb : ∀ u ∈ Icc a b, |g u| ≤ C)
    (hh : IntervalIntegrable h volume a b)
    (hH : ∀ x ∈ Icc a b, ‖∫ u in x..b, h u‖ ≤ B) :
    ‖∫ u in a..b, g u • h u‖ ≤ 3 * C * B := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hH b hbI)
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hgb a haI)
  set f : ℝ → ℝ := fun u => g u + C with hf
  have hfm : MonotoneOn f (Icc a b) := fun x hx y hy hxy => by
    simp only [hf]; linarith [hg hx hy hxy]
  have hfa : 0 ≤ f a := by
    simp only [hf]; linarith [neg_abs_le (g a), hgb a haI]
  obtain ⟨ξ, hξ, hle⟩ :=
    exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn hab hfa hfm hh
  have hfi : IntervalIntegrable (fun x ↦ f x • h x) volume a b :=
    intervalIntegrable_iff.2 <| hh.def'.smul_of_top_right <|
      (hfm.memLp_isCompact isCompact_Icc).mono_measure <|
        Measure.restrict_mono_set volume (uIcc_of_le hab ▸ uIoc_subset_uIcc)
  have hci : IntervalIntegrable (fun x ↦ C • h x) volume a b := hh.smul C
  have heq : (∫ u in a..b, g u • h u) = (∫ u in a..b, f u • h u) - ∫ u in a..b, C • h u := by
    rw [← intervalIntegral.integral_sub hfi hci]
    congr 1; ext u; simp only [hf]; rw [add_smul]; abel
  rw [heq, intervalIntegral.integral_smul]
  have hfb : f b ≤ 2 * C := by
    simp only [hf]; linarith [le_abs_self (g b), hgb b hbI]
  have h1 : ‖∫ u in a..b, f u • h u‖ ≤ 2 * C * B :=
    hle.trans (mul_le_mul hfb (hH ξ hξ) (norm_nonneg _) (by linarith))
  have h2 : ‖C • ∫ u in a..b, h u‖ ≤ C * B := by
    rw [norm_smul, Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left (hH a haI) hC
  calc _ ≤ ‖∫ u in a..b, f u • h u‖ + ‖C • ∫ u in a..b, h u‖ := norm_sub_le _ _
    _ ≤ 2 * C * B + C * B := add_le_add h1 h2
    _ = 3 * C * B := by ring

/-- The monotone case of Lemma 1. -/
theorem lemma1_mono (a b m M : ℝ) (F F' G : ℝ → ℝ) (hab : a ≤ b) (hm : 0 < m)
    (hF : ∀ u ∈ Set.Icc a b, HasDerivAt F (F' u) u) (hF' : ContinuousOn F' (Set.Icc a b))
    (hG : ContinuousOn G (Set.Icc a b))
    (hmono : MonotoneOn (fun u => G u / F' u) (Set.Icc a b))
    (hFm : ∀ u ∈ Set.Icc a b, m ≤ |F' u|) (hGM : ∀ u ∈ Set.Icc a b, |G u| ≤ M) :
    ‖∫ u in a..b, (G u : ℂ) * ee (F u)‖ ≤ 1 * M / m := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  set h : ℝ → ℂ := fun u => (F' u : ℂ) * ee (F u) with hhdef
  set E : ℝ → ℂ := fun u => ee (F u) / (2 * π * I) with hE
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hEd : ∀ u ∈ Icc a b, HasDerivAt E (h u) u := by
    intro u hu
    have h1 : HasDerivAt (fun u => ((F u : ℝ) : ℂ)) (F' u) u := (hF u hu).ofReal_comp
    have h2 := ((h1.const_mul (2 * π * I : ℂ)).cexp).div_const (2 * π * I)
    convert h2 using 1
    all_goals first
      | (simp only [hE, ee]; done)
      | (show (F' u : ℂ) * ee (F u) = _; simp only [ee]; field_simp)
  have hFc : ContinuousOn F (Icc a b) := fun u hu => (hF u hu).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc a b) := by
    simp only [hhdef, ee]
    exact (continuous_ofReal.comp_continuousOn hF').mul
      ((continuous_const.mul continuous_ofReal).cexp.comp_continuousOn hFc)
  have hhi : ∀ x ∈ Icc a b, IntervalIntegrable h volume x b := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.2]
    exact hhc.mono (Icc_subset_Icc hx.1 le_rfl)
  have hnE : ∀ u, ‖E u‖ = 1 / (2 * π) := by
    intro u
    simp only [hE, ee, norm_div]
    rw [show (2 * π * I : ℂ) * (F u : ℂ) = ((2 * π * F u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    simp [abs_of_pos Real.pi_pos]
  have hH : ∀ x ∈ Icc a b, ‖∫ u in x..b, h u‖ ≤ 1 / π := by
    intro x hx
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := E)
      (fun u hu => hEd u (by rw [uIcc_of_le hx.2] at hu; exact ⟨hx.1.trans hu.1, hu.2⟩))
      (hhi x hx)]
    calc _ ≤ ‖E b‖ + ‖E x‖ := norm_sub_le _ _
      _ = 1 / π := by rw [hnE, hnE]; field_simp; ring
  have hF0 : ∀ u ∈ Icc a b, F' u ≠ 0 := fun u hu h0 => by
    have := hFm u hu; rw [h0, abs_zero] at this; linarith
  have hgb : ∀ u ∈ Icc a b, |G u / F' u| ≤ M / m := by
    intro u hu
    rw [abs_div]
    have hp : 0 < |F' u| := abs_pos.2 (hF0 u hu)
    rw [div_le_div_iff₀ hp hm]
    have hM : 0 ≤ M := (abs_nonneg _).trans (hGM u hu)
    nlinarith [hGM u hu, hFm u hu, abs_nonneg (G u)]
  have heq : (∫ u in a..b, (G u : ℂ) * ee (F u)) = ∫ u in a..b, (G u / F' u) • h u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [hI] at hu
    simp only [hhdef, Complex.real_smul]
    have := hF0 u hu
    push_cast
    rw [← mul_assoc, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 this)]
  rw [heq]
  have key := lemma1_smvt_bound a b (M / m) (1 / π) _ h hab hmono hgb
    (hhi a ⟨le_rfl, hab⟩) hH
  have hMm : 0 ≤ M / m := (abs_nonneg _).trans (hgb a ⟨le_rfl, hab⟩)
  refine key.trans ?_
  have : 3 * (M / m) * (1 / π) ≤ M / m := by
    rw [mul_one_div, div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  rw [one_mul]; linarith

/-- Lemma 1 of Zhan 1991, page 261, from Titchmarsh Lemma 4.3, with `K = 1`. -/
theorem zhan_lemma1_proof : Lemma1 := by
  refine ⟨1, ?_⟩
  intro a b m M F F' G hab hm hF hF' hG hmon hFm hGM
  rcases hmon with hmon | hanti
  · exact lemma1_mono a b m M F F' G hab hm hF hF' hG hmon hFm hGM
  · have h := lemma1_mono a b m M F F' (fun u => -G u) hab hm hF hF' hG.neg
      (by
        have := hanti.neg
        intro x hx y hy hxy
        have := this hx hy hxy
        simp only at this
        simp only [neg_div]; exact this)
      hFm (fun u hu => by rw [abs_neg]; exact hGM u hu)
    have he : (∫ u in a..b, ((-G u : ℝ) : ℂ) * ee (F u)) = -∫ u in a..b, (G u : ℂ) * ee (F u) := by
      rw [← intervalIntegral.integral_neg]; congr 1; ext u; push_cast; ring
    rw [he, norm_neg] at h
    exact h

end

end LeanLab.Zhan1991
