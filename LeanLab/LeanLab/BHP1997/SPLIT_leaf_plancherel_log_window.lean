/-
Route burst burst-20261124, session S4, KEEP GOING after unit S4-28, BHP1997, split of
`S64LowExcCharNP.leaf_plancherel_log_window` in SPLIT_leaf_gallagher_mean_value.lean.

P0069 Baker Harman Pintz 1997, page 44, proof of Lemma 29, the variant of [8] Lemma 2, in
the scale free form on the window `u ∈ [log(1/2), log 3]`. Gallagher's proof of [8] Lemma 2
majorises the window by a smooth weight with a positive Fourier transform. This file takes
the Gaussian weight `w(u) = exp(-u^2/4)`:
* `leaf_gaussian_weighted_mean_value`: the weighted mean value over the whole line,
  `∫ w(u) |∫_{-T}^{T} h(t) e^(itu) dt|^2 du ≪ ∫_{-T}^{T} |h(t)|^2 dt`. CITED [8] Lemma 2,
  Gallagher 1970; it holds with constant `2π` since the Fourier transform of `w` is
  `2 √π exp(-x^2)`.
* `leaf_plancherel_log_window_of_leaves`: PROVED from that leaf. On the window `|u| ≤ 2`,
  so `w(u) ≥ e^(-1) ≥ 1/3`; the weighted integrand is integrable because the inner integral
  is bounded by `∫ |h|` and the Gaussian is integrable.
`leaf_plancherel_log_window_split_twin` checks the exact statement of the earlier leaf.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.SPLIT_leaf_gallagher_mean_value

namespace LeanLab.BHP1997.S64LowExcCharNP
open Complex MeasureTheory

/-- LEAF: page 44, proof of Lemma 29, the variant of [8] Lemma 2 with the Gaussian weight,
class HARD. P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2": with
`w(u) = exp(-u^2/4)`, `∫_ℝ w(u) |∫_{-T}^{T} h(t) e^(itu) dt|^2 du ≪ ∫_{-T}^{T} |h(t)|^2 dt`
for continuous `h`. Expanding the square and integrating in `u` first gives the kernel
`ŵ(t - s) = 2 √π exp(-(t-s)^2)`, and `|h(t) h(s)| ≤ (|h(t)|^2 + |h(s)|^2)/2` gives the
constant `2π`. CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gaussian_weighted_mean_value :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ h : ℝ → ℂ, Continuous h →
      ∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) *
          ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 ≤
        K * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
  sorry

/-- Page 44, proof of Lemma 29: the scale free form of the variant of [8] Lemma 2 on the
window `[log(1/2), log 3]`, PROVED from `leaf_gaussian_weighted_mean_value`, since the
Gaussian weight is at least `1/3` on the window. -/
theorem leaf_plancherel_log_window_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ h : ℝ → ℂ, Continuous h →
      ∫ u in (Real.log (1 / 2))..(Real.log 3),
          ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 ≤
        K * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := leaf_gaussian_weighted_mean_value
  refine ⟨3 * K, by positivity, ?_⟩
  intro T hT h hh
  have hlogle : Real.log (1 / 2) ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  set F : ℝ → ℂ := fun u => ∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I)) with hFdef
  have hFc : Continuous F := by
    have hu : Continuous fun p : ℝ × ℝ => h p.2 * cexp ((p.1 : ℂ) * ((p.2 : ℂ) * I)) :=
      (hh.comp continuous_snd).mul (Continuous.cexp (by fun_prop))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu _ _
  have hnorm1 : ∀ u t : ℝ, ‖h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ = ‖h t‖ := by
    intro u t
    rw [norm_mul, show (u : ℂ) * ((t : ℂ) * I) = ((u * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hFb : ∀ u, ‖F u‖ ≤ ∫ t in (-T)..T, ‖h t‖ := by
    intro u
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (le_of_eq ?_)
    exact intervalIntegral.integral_congr (fun t _ => hnorm1 u t)
  set M : ℝ := ∫ t in (-T)..T, ‖h t‖ with hMdef
  have hwc : Continuous fun u : ℝ => Real.exp (-(1 / 4) * u ^ 2) := by fun_prop
  have hint : Integrable (fun u : ℝ => Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2) := by
    have hg := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (M ^ 2)
    refine hg.mono' (hwc.mul (hFc.norm.pow 2)).aestronglyMeasurable ?_
    refine ae_of_all _ (fun u => ?_)
    have hF0 : 0 ≤ ‖F u‖ := norm_nonneg _
    have hFM : ‖F u‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hF0 (hFb u) 2
    have hw0 : 0 < Real.exp (-(1 / 4) * u ^ 2) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2
        ≤ Real.exp (-(1 / 4) * u ^ 2) * M ^ 2 := mul_le_mul_of_nonneg_left hFM hw0.le
      _ = M ^ 2 * Real.exp (-(1 / 4) * u ^ 2) := by ring
  have hwin : ∫ u in (Real.log (1 / 2))..(Real.log 3), ‖F u‖ ^ 2 ≤
      ∫ u in (Real.log (1 / 2))..(Real.log 3),
        3 * (Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on hlogle
    · exact (hFc.norm.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul (hwc.mul (hFc.norm.pow 2))).intervalIntegrable _ _
    · intro u hu
      have hl2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
      have hlo : -1 ≤ u := by
        have := Real.log_two_lt_d9
        linarith [hu.1]
      have hup : u ≤ 2 := by
        have h3 : Real.log 3 ≤ 2 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          linarith [Real.add_one_le_exp (2 : ℝ)]
        linarith [hu.2]
      have hsq : u ^ 2 ≤ 4 := by nlinarith
      have hw : 1 / 3 ≤ Real.exp (-(1 / 4) * u ^ 2) := by
        have h1 : -1 ≤ -(1 / 4) * u ^ 2 := by nlinarith
        have h2 : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le (Real.exp_pos 1)
            (by linarith [Real.exp_one_lt_d9])
        exact h2.trans (Real.exp_le_exp.mpr h1)
      have hp := mul_le_mul_of_nonneg_right hw (sq_nonneg ‖F u‖)
      nlinarith
  rw [intervalIntegral.integral_const_mul] at hwin
  have hsub : ∫ u in (Real.log (1 / 2))..(Real.log 3),
        Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2 ≤
      ∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hlogle]
    refine setIntegral_le_integral hint (ae_of_all _ (fun u => ?_))
    show (0 : ℝ) ≤ Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2
    positivity
  have hK' := hK T hT h hh
  calc _ ≤ 3 * ∫ u in (Real.log (1 / 2))..(Real.log 3),
        Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2 := hwin
    _ ≤ 3 * ∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) * ‖F u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsub (by norm_num)
    _ ≤ 3 * (K * ∫ t in (-T)..T, ‖h t‖ ^ 2) := mul_le_mul_of_nonneg_left hK' (by norm_num)
    _ = 3 * K * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by ring

/-- The split closes exactly the statement of `leaf_plancherel_log_window`. -/
theorem leaf_plancherel_log_window_split_twin :
    type_of% @leaf_plancherel_log_window :=
  leaf_plancherel_log_window_of_leaves

end LeanLab.BHP1997.S64LowExcCharNP

#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_plancherel_log_window_of_leaves
