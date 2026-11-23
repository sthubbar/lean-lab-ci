import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_high_half_le
import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_low_half_le
import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_low_window_le

/-!
Counterexamples to eight window leaves of the split of `positive_mass_norm_sum_integral`,
P0014 Lemma 4.4 and Proposition 4.6, arXiv 1305.2897 pages 38 to 44.

The parent statement `positive_mass_norm_sum_integral` carries the hypothesis
`2 * π * exp 2 ≤ q * T`. The window leaves dropped it, and each of the eight leaves treated here
bounds a nonnegative zero sum by a positive multiple of the mean weight integral
`(1 / (2 * π)) * ∫ t in 1..T, ‖F_δ (1/2 + i t)‖ * log (q t / (2 π))` alone. At modulus `q = 1`,
height `T = 2` and `δ = 0` the logarithm is negative on the whole interval `[1, 2]`, and the
Gaussian Mellin transform `F_0 (s) = 2⁻¹ 2^(s/2) Γ (s/2)` has no zero on the critical line, so
the right side is strictly negative while the left side is a sum of norms. Each leaf is
therefore false as stated, for every character modulo one.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.WindowFalse1122
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- The Gaussian Mellin transform at `δ = 0` in closed form, `F_0 (s) = 2⁻¹ (1/2)^(-s/2) Γ (s/2)`
for `0 < re s`: the substitution `u = t ^ 2 / 2` in the Mellin integral of page 43. -/
theorem gaussianMellin_zero_eq (s : ℂ) (hs : 0 < s.re) :
    gaussianMellin 0 s =
      ((|(2:ℝ)|⁻¹ : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)) := by
  have h1 : gaussianMellin 0 s =
      mellin (fun t : ℝ => (fun u : ℝ => (fun v : ℝ => ((exp (-v) : ℝ) : ℂ)) ((1 / 2 : ℝ) * u))
        (t ^ (2 : ℝ))) s := by
    unfold gaussianMellin mellin
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [e, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      Real.rpow_two]
    congr 3
    ring
  have hs2 : 0 < (s / 2).re := by simp; positivity
  refine h1.trans ((mellin_comp_rpow
    (fun u : ℝ => (fun v : ℝ => ((exp (-v) : ℝ) : ℂ)) ((1 / 2 : ℝ) * u)) s 2).trans ?_)
  rw [mellin_comp_mul_left (fun v : ℝ => ((exp (-v) : ℝ) : ℂ)) _ (by norm_num : (0:ℝ) < 1 / 2),
    ← Complex.GammaIntegral_eq_mellin]
  push_cast
  rw [← Complex.Gamma_eq_integral hs2, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

/-- `F_0` has no zero in the right half plane, since `Γ` has none. -/
theorem gaussianMellin_zero_ne_zero (s : ℂ) (hs : 0 < s.re) : gaussianMellin 0 s ≠ 0 := by
  have hs2 : 0 < (s / 2).re := by simp; positivity
  rw [gaussianMellin_zero_eq s hs]
  refine mul_ne_zero (by norm_num) (mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hs2))
  rw [Ne, Complex.cpow_eq_zero_iff]
  norm_num

/-- `F_0` is continuous along the critical line, from the closed form. -/
theorem continuous_gaussianMellin_zero_line :
    Continuous (fun t : ℝ => gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)) := by
  have hre : ∀ t : ℝ, 0 < ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re := by intro t; simp
  have heq : (fun t : ℝ => gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)) =
      fun t : ℝ => ((|(2:ℝ)|⁻¹ : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) ^
        (-(((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2)) *
        Complex.Gamma (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2)) := by
    funext t; exact gaussianMellin_zero_eq _ (hre t)
  rw [heq]
  have hlin : Continuous (fun t : ℝ => ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2) := by fun_prop
  have hG : Continuous (fun t : ℝ => Complex.Gamma (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2)) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    refine ((Complex.differentiableAt_Gamma _ fun m hm => ?_).continuousAt).comp hlin.continuousAt
    have := congrArg Complex.re hm
    simp at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hP : Continuous (fun t : ℝ => ((1 / 2 : ℝ) : ℂ) ^
      (-(((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2))) :=
    Continuous.const_cpow hlin.neg (Or.inl (by norm_num))
  exact continuous_const.mul (hP.mul hG)

/-- The mean weight integral at modulus one and height two is strictly negative: on `[1, 2]`
the logarithm `log (t / (2 π))` is negative and `‖F_0 (1/2 + i t)‖` is positive. -/
theorem mean_weight_integral_neg :
    (∫ t in (1 : ℝ)..2, ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
      log (((1 : ℕ) : ℝ) * t / (2 * π))) < 0 := by
  have hcont : ContinuousOn (fun t : ℝ => -(‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
      log (((1 : ℕ) : ℝ) * t / (2 * π)))) (Set.uIcc 1 2) := by
    refine ContinuousOn.neg (ContinuousOn.mul
      continuous_gaussianMellin_zero_line.norm.continuousOn ?_)
    refine ContinuousOn.log (by fun_prop) fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on hcont.intervalIntegrable
    (fun t ht => by
      have hn : 0 < ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ :=
        norm_pos_iff.2 (gaussianMellin_zero_ne_zero _ (by simp))
      have ht0 : (0:ℝ) < ((1 : ℕ) : ℝ) * t / (2 * π) := by
        have : (0:ℝ) < t := by linarith [ht.1]
        positivity
      have ht1 : ((1 : ℕ) : ℝ) * t / (2 * π) < 1 := by
        rw [div_lt_one (by positivity)]
        have := Real.pi_gt_three
        push_cast; linarith [ht.2]
      have hl : log (((1 : ℕ) : ℝ) * t / (2 * π)) < 0 := Real.log_neg ht0 ht1
      nlinarith)
    (by norm_num : (1:ℝ) < 2)
  rw [intervalIntegral.integral_neg] at hpos
  linarith

/-- The common shape of the eight counterexamples: at `q = 1`, `δ = 0`, `T = 2`, a window sum of
norms is not bounded by any positive multiple of the mean weight integral. -/
theorem window_not_le (χ : DirichletCharacter ℂ 1) (c : ℝ) (hc : 0 < c)
    (S : Set {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)}) :
    ¬ ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)},
        Set.indicator S (fun ρ => ‖mellinMassTerm χ 0 ρ.val‖) ρ) ≤
      c * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..2,
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log (((1 : ℕ) : ℝ) * t / (2 * π))))) := by
  intro h
  have h0 : 0 ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ (2 : ℝ)},
        Set.indicator S (fun ρ => ‖mellinMassTerm χ 0 ρ.val‖) ρ :=
    tsum_nonneg fun ρ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  have hI := mean_weight_integral_neg
  have hneg : c * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..2,
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log (((1 : ℕ) : ℝ) * t / (2 * π)))) < 0 :=
    mul_neg_of_pos_of_neg hc (mul_neg_of_pos_of_neg (by positivity) hI)
  linarith

/-- FALSE: the leaf `positive_mass_window_two_le` of `SPLIT_positive_mass_norm_sum_integral.lean`, stated for all `q`, `χ`, `δ`, `T` with `1 ≤ T`,
fails at `q = 1`, any `χ`, `δ = 0`, `T = 2`: its right side is `1 / 2` times the strictly negative
mean weight integral of `mean_weight_integral_neg`. -/
theorem positive_mass_window_two_le_false :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) := fun h =>
  window_not_le 1 (1 / 2) (by norm_num) _ (h 1 1 0 2 (by norm_num))

/-- FALSE: the leaf `positive_mass_window_one_high_half_le` of `SPLIT_positive_mass_window_one_le.lean`, stated for all `q`, `χ`, `δ`, `T` with `1 ≤ T`,
fails at `q = 1`, any `χ`, `δ = 0`, `T = 2`: its right side is `1 / 4` times the strictly negative
mean weight integral of `mean_weight_integral_neg`. -/
theorem positive_mass_window_one_high_half_le_false :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) := fun h =>
  window_not_le 1 (1 / 4) (by norm_num) _ (h 1 1 0 2 (by norm_num))

/-- FALSE: the leaf `positive_mass_window_two_low_window_le` of `SPLIT_positive_mass_window_two_le.lean`, stated for all `q`, `χ`, `δ`, `T` with `1 ≤ T`,
fails at `q = 1`, any `χ`, `δ = 0`, `T = 2`: its right side is `1 / 4` times the strictly negative
mean weight integral of `mean_weight_integral_neg`. -/
theorem positive_mass_window_two_low_window_le_false :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) := fun h =>
  window_not_le 1 (1 / 4) (by norm_num) _ (h 1 1 0 2 (by norm_num))

/-- FALSE: the leaf `positive_mass_window_two_high_window_le` of `SPLIT_positive_mass_window_two_le.lean`, stated for all `q`, `χ`, `δ`, `T` with `1 ≤ T`,
fails at `q = 1`, any `χ`, `δ = 0`, `T = 2`: its right side is `1 / 4` times the strictly negative
mean weight integral of `mean_weight_integral_neg`. -/
theorem positive_mass_window_two_high_window_le_false :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) := fun h =>
  window_not_le 1 (1 / 4) (by norm_num) _ (h 1 1 0 2 (by norm_num))

/-- FALSE: the leaf `positive_mass_window_one_low_half_upper_quarter_le` of `SPLIT_positive_mass_window_one_low_half_le.lean`, stated for all `q`, `χ`, `δ`, `T` with `1 ≤ T`,
fails at `q = 1`, any `χ`, `δ = 0`, `T = 2`: its right side is `1 / 8` times the strictly negative
mean weight integral of `mean_weight_integral_neg`. -/
theorem positive_mass_window_one_low_half_upper_quarter_le_false :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 9 / 8 < ρ.val.im ∧ ρ.val.im ≤ 5 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) := fun h =>
  window_not_le 1 (1 / 8) (by norm_num) _ (h 1 1 0 2 (by norm_num))

/-- FALSE: the leaf `positive_mass_window_two_low_window_low_half_le` of `SPLIT_positive_mass_window_two_low_window_le.lean`, stated for all `q`, `χ`, `δ`, `T` with `1 ≤ T`,
fails at `q = 1`, any `χ`, `δ = 0`, `T = 2`: its right side is `1 / 8` times the strictly negative
mean weight integral of `mean_weight_integral_neg`. -/
theorem positive_mass_window_two_low_window_low_half_le_false :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 13 / 8}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) := fun h =>
  window_not_le 1 (1 / 8) (by norm_num) _ (h 1 1 0 2 (by norm_num))

/-- FALSE: the leaf `positive_mass_window_two_low_window_high_half_le` of `SPLIT_positive_mass_window_two_low_window_le.lean`, stated for all `q`, `χ`, `δ`, `T` with `1 ≤ T`,
fails at `q = 1`, any `χ`, `δ = 0`, `T = 2`: its right side is `1 / 8` times the strictly negative
mean weight integral of `mean_weight_integral_neg`. -/
theorem positive_mass_window_two_low_window_high_half_le_false :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 13 / 8 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) := fun h =>
  window_not_le 1 (1 / 8) (by norm_num) _ (h 1 1 0 2 (by norm_num))

/-- FALSE: the leaf `high_half_weight_pos_part_le` of
`SPLIT_positive_mass_window_one_high_half_le.lean` fails at `q = 1`, `δ = 0`, `T = 2`: the
positive part `max (log (t / (2 π))) 0` vanishes on `[1, 2]`, so the left side is zero, while the
right side is a quarter of the strictly negative mean weight integral. -/
theorem high_half_weight_pos_part_le_false :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          max (log ((q : ℝ) * t / (2 * π))) 0)) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) := by
  intro h
  have h1 := h 1 1 0 2 (by norm_num)
  have hz : (∫ t in (1 : ℝ)..2,
      ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
        max (log (((1 : ℕ) : ℝ) * t / (2 * π))) 0) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun t ht => ?_)]
    · simp
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht0 : (0:ℝ) < ((1 : ℕ) : ℝ) * t / (2 * π) := by
      have : (0:ℝ) < t := by linarith [ht.1]
      positivity
    have ht1 : ((1 : ℕ) : ℝ) * t / (2 * π) < 1 := by
      rw [div_lt_one (by positivity)]
      have := Real.pi_gt_three
      push_cast; linarith [ht.2]
    have hl : log (((1 : ℕ) : ℝ) * t / (2 * π)) < 0 := Real.log_neg ht0 ht1
    simp only [max_eq_right hl.le, mul_zero]
  rw [hz] at h1
  have hI := mean_weight_integral_neg
  have : (1 / 4 : ℝ) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..2,
        ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log (((1 : ℕ) : ℝ) * t / (2 * π)))) < 0 :=
    mul_neg_of_pos_of_neg (by norm_num) (mul_neg_of_pos_of_neg (by positivity) hI)
  linarith

end LeanLab.HelfgottMajor.WindowFalse1122
