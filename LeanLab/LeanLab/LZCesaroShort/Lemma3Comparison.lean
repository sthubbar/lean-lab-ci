import LeanLab.LZCesaroShort.Circle2

/-!
# The elementary comparison step for P0058 Lemma 3

AI wrote this Lean code. Binary Goldbach is open.
The source is arXiv 1606.00869v2, page 3, Lemmas 3 and 4.
This file isolates the effect of a bounded perturbation on a mean square.
It does not assume RH or the asymptotic in Lemma 3.
-/

namespace LeanLab.LZCesaroShort

open MeasureTheory

/-- A bounded perturbation changes the square of a norm by a controlled amount. -/
lemma norm_sq_perturbation (z u : ℂ) {C : ℝ} (_hC : 0 ≤ C) (hu : ‖u‖ ≤ C) :
    |‖z + u‖ ^ 2 - ‖z‖ ^ 2| ≤ 2 * C * ‖z‖ + C ^ 2 := by
  have hz := norm_nonneg z
  have hu0 := norm_nonneg u
  have hzu := norm_nonneg (z + u)
  have hupper := norm_add_le z u
  have hlower : ‖z‖ ≤ ‖z + u‖ + ‖u‖ := by
    simpa using norm_sub_le (z + u) u
  have hu2 : ‖u‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hu0 hu 2
  have hmul : 2 * ‖z‖ * ‖u‖ ≤ 2 * C * ‖z‖ := by nlinarith
  rw [abs_le]
  constructor
  · have hd : ‖z‖ - ‖z + u‖ ≤ C := by linarith
    have hm := mul_le_mul_of_nonneg_left hd hz
    nlinarith [sq_nonneg (‖z‖ - ‖z + u‖)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hupper)
      (show 0 ≤ ‖z + u‖ + (‖z‖ + ‖u‖) by positivity)]

/-- Mean squares on the unit interval are stable under a bounded perturbation. -/
theorem mean_square_perturbation {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 < B)
    (hfg : ∀ α ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖g α - f α‖ ≤ C)
    (hfB : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖f α‖ ^ 2 ≤ B) :
    |(∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖ ^ 2)
      - ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖f α‖ ^ 2|
      ≤ 2 * C * Real.sqrt B + C ^ 2 := by
  have hiF := (hf.norm.pow 2).intervalIntegrable (μ := volume) (-(1 / 2 : ℝ)) (1 / 2)
  have hiG := (hg.norm.pow 2).intervalIntegrable (μ := volume) (-(1 / 2 : ℝ)) (1 / 2)
  have hpt : ∀ α ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
      |‖g α‖ ^ 2 - ‖f α‖ ^ 2| ≤ 2 * C * ‖f α‖ + C ^ 2 := by
    intro α hα
    have h := norm_sq_perturbation (f α) (g α - f α) hC (hfg α hα)
    rw [show f α + (g α - f α) = g α by ring] at h
    exact h
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)
    (((hg.norm.pow 2).sub (hf.norm.pow 2)).abs.intervalIntegrable _ _)
    (((continuous_const.mul hf.norm).add continuous_const).intervalIntegrable _ _) hpt
  change (∫ α in (-(1 / 2 : ℝ))..(1 / 2), |‖g α‖ ^ 2 - ‖f α‖ ^ 2|)
    ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), (2 * C * ‖f α‖ + C ^ 2) at hmono
  have hint : (∫ α in (-(1 / 2 : ℝ))..(1 / 2), (2 * C * ‖f α‖ + C ^ 2))
      = 2 * C * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖f α‖) + C ^ 2 := by
    rw [intervalIntegral.integral_add (f := fun α => 2 * C * ‖f α‖)
      (g := fun _ => C ^ 2)
      ((continuous_const.mul hf.norm).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    norm_num
  rw [hint] at hmono
  have hnorm := integral_norm_le_sqrt hf hB hfB
  calc
    _ = |∫ α in (-(1 / 2 : ℝ))..(1 / 2), (‖g α‖ ^ 2 - ‖f α‖ ^ 2)| := by
      rw [intervalIntegral.integral_sub (f := fun α => ‖g α‖ ^ 2)
        (g := fun α => ‖f α‖ ^ 2) hiG hiF]
    _ ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), |‖g α‖ ^ 2 - ‖f α‖ ^ 2| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ 2 * C * (∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖f α‖) + C ^ 2 := hmono
    _ ≤ _ := by nlinarith

/-- The Parseval coefficient moment differs from the mean square by an explicit error. -/
theorem lemma3_comparison {N : ℕ} (hN : (10 : ℝ) ^ 20 ≤ N) :
    |(∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖St N α - 1 / zz N α‖ ^ 2)
      - ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n - 1) ^ 2 * Real.exp (-2 * n / N)|
      ≤ 16 * Real.sqrt (2 * N * Real.log N + N + 130) + 64 := by
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hB : 0 < 2 * N * Real.log N + N + 130 := by positivity
  let f : ℝ → ℂ := fun α => St N α - 1 / zz N α
  let g : ℝ → ℂ := fun α => St N α - Wz N α
  have hf : Continuous f := (continuous_St hNn).sub
    (continuous_const.div (continuous_zz N) (zz_ne_zero hNn))
  have hg : Continuous g := (continuous_St hNn).sub (continuous_Wz hNn)
  have hfg : ∀ α ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖g α - f α‖ ≤ 8 := by
    intro α hα
    have hre : (zz N α).re = 1 / N := by simp [zz]
    have him : (zz N α).im = -(2 * Real.pi * α) := by simp [zz]
    have hαb : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
    have hb := LeanLab.PNTPort.Selberg.geom_sub_inv_le (z := zz N α)
      (by rw [hre]; positivity)
      (by rw [hre, div_le_one hN0]; exact hN1)
      (by
        rw [him, abs_neg, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        nlinarith [Real.pi_pos])
    have heq : g α - f α = -(Wz N α - 1 / zz N α) := by dsimp [f, g]; ring
    rw [heq, norm_neg]
    exact hb
  have hcomp := mean_square_perturbation hf hg (by norm_num : (0 : ℝ) ≤ 8)
    hB hfg (lemma3_upper N hN)
  have hparseval : (∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖g α‖ ^ 2)
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n - 1) ^ 2 * Real.exp (-2 * n / N) := by
    dsimp [g]
    simp_rw [D_eq hNn]
    rw [parseval_tsum _ (summable_dc hNn)]
    apply tsum_congr
    intro n
    simp only [dc, LeanLab.PNTPort.Gallagher.lam1, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have he : Real.exp (-(n / N)) ^ 2 = Real.exp (-2 * n / N) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  rw [hparseval, abs_sub_comm] at hcomp
  convert hcomp using 1
  norm_num

/-- Lemma 3 follows from its coefficient moment asymptotic, with no RH input. -/
theorem lemma3_of_moment (hM : (∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n - 1) ^ 2 * Real.exp (-2 * n / N))
      - N / 2 * Real.log N| ≤ K * N)) : Lemma3 := by
  obtain ⟨K, N₀, hM⟩ := hM
  refine ⟨96 + |K|, max N₀ (10 ^ 20), fun N hN => ?_⟩
  have hlarge : (10 : ℝ) ^ 20 ≤ N := by
    exact_mod_cast le_trans (le_max_right N₀ (10 ^ 20)) hN
  have hN1 : (1 : ℝ) ≤ N := le_trans (by norm_num) hlarge
  have hN130 : (130 : ℝ) ≤ N := le_trans (by norm_num) hlarge
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hN0).mpr
    have := Real.exp_one_lt_d9
    linarith
  have hslog : 1 ≤ Real.sqrt (Real.log N) := by
    simpa using Real.sqrt_le_sqrt hlog
  have hNs : 1 ≤ (N : ℝ) * Real.sqrt (Real.log N) := by nlinarith
  have hB4 : 2 * N * Real.log N + N + 130 ≤ 4 * N * Real.log N := by
    nlinarith
  have hBsq : 2 * N * Real.log N + N + 130
      ≤ (2 * N * Real.sqrt (Real.log N)) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hN1
      (by positivity : 0 ≤ 4 * (N : ℝ) * Real.log N)
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ Real.log N)]
    nlinarith
  have hsB : Real.sqrt (2 * N * Real.log N + N + 130)
      ≤ 2 * N * Real.sqrt (Real.log N) := by
    calc _ ≤ Real.sqrt ((2 * N * Real.sqrt (Real.log N)) ^ 2) :=
        Real.sqrt_le_sqrt hBsq
      _ = _ := Real.sqrt_sq (by positivity)
  have hc := lemma3_comparison hlarge
  have hm := hM N (le_trans (le_max_left _ _) hN)
  have hm' : |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n - 1) ^ 2 * Real.exp (-2 * n / N))
      - N / 2 * Real.log N| ≤ |K| * N * Real.sqrt (Real.log N) := by
    refine hm.trans ?_
    have hk := le_abs_self K
    have h1 := mul_le_mul_of_nonneg_right hk hN0.le
    have h2 := mul_le_mul_of_nonneg_left hslog
      (by positivity : 0 ≤ |K| * (N : ℝ))
    nlinarith
  have ht := abs_sub_le
    (∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖St N α - 1 / zz N α‖ ^ 2)
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n - 1) ^ 2 * Real.exp (-2 * n / N))
    (N / 2 * Real.log N)
  nlinarith

end LeanLab.LZCesaroShort
