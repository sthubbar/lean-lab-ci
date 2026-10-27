import LeanLab.LZCesaroShort.CircleY

/-!
# `I₁` for `H ≤ N`

Lab file, unit U-6207, CLOUD 20261020T0817Z-cloud38. AI wrote this file: `I1_bound` of
`Circle.lean` and `I1_boundY` of `CircleY.lean` with `H ≤ N` in place of `H < N`; their proofs
used only `H ≤ N`. No cited input.
-/

namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher LeanLab.PNTPort.Selberg
local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-- **`I₁`**, from Lemma 2. -/
theorem I1_bound_le {N H : ℕ} (hN : 1 ≤ N) (hHN : H ≤ N) :
    ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (1 / zz N α) ^ 2)
      - ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ)‖
      ≤ (H : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ α, TH N H H (-α) * (1 / zz N α) ^ 2 = ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n : ℝ) : ℂ) * (eL (-(n * α)) * (1 / zz N α) ^ 2) := by
    intro α; rw [TH_full, sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ) * -α = -(n * α) by ring]; ring
  have hcz : Continuous (fun α => (1 / zz N α) ^ 2) :=
    (continuous_const.div (continuous_zz N) (zz_ne_zero hN)).pow 2
  simp_rw [hpt]
  have hsw : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n : ℝ) : ℂ) * (eL (-(n * α)) * (1 / zz N α) ^ 2)
      = ∑ n ∈ Icc (N - H) (N + H), ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
      ((tw N H n : ℝ) : ℂ) * (eL (-(n * α)) * (1 / zz N α) ^ 2) :=
    intervalIntegral.integral_finset_sum fun n _ => (continuous_const.mul
      (((continuous_e.comp (continuous_const.mul continuous_id).neg)).mul hcz)).intervalIntegrable _ _
  rw [hsw, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [← sum_tw hHN, ← div_one (∑ n ∈ Icc (N - H) (N + H), tw N H n)]
  rw [div_one]
  refine sum_le_sum fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with h0 | _
  · have hHN' : H = N := by rw [mem_Icc] at hn; omega
    have htw : tw N H n = 0 := by subst h0; rw [hHN']; unfold tw; simp
    simp [htw]
  have hn1 : 1 ≤ n := by rw [mem_Icc] at hn; omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [intervalIntegral.integral_const_mul]
  have hI : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), eL (-(n * α)) * (1 / zz N α) ^ 2
      = ∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine setIntegral_congr_fun measurableSet_Ioc fun α _ => ?_
    rw [e_neg_eq, zz_eq, one_div_pow]
  have h2' := lemma2 hN0 hnr
  rw [hI]
  have e1 : ((tw N H n : ℝ) : ℂ) * (∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
        Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2))
      - ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ)
      = ((tw N H n : ℝ) : ℂ) * ((∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
        Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2))
        - ((n * Real.exp (-n / N) : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tw_nonneg hHN hn)]
  have hpi : 1 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  calc tw N H n * ‖_‖ ≤ tw N H n * (1 / Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left h2' (tw_nonneg hHN hn)
    _ ≤ tw N H n * 1 := mul_le_mul_of_nonneg_left hpi (tw_nonneg hHN hn)
    _ = tw N H n := mul_one _

/-- **`I₁`**, from Lemma 2. -/
theorem I1_boundY_le {N H : ℕ} {y : ℝ} (hN : 1 ≤ N) (hHN : H ≤ N) :
    ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H y (-α) * (1 / zz N α) ^ 2)
      - ∑ n ∈ Fy N H y, ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ)‖
      ≤ (H : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ α, TH N H y (-α) * (1 / zz N α) ^ 2 = ∑ n ∈ Fy N H y,
      ((tw N H n : ℝ) : ℂ) * (eL (-(n * α)) * (1 / zz N α) ^ 2) := by
    intro α; rw [TH_eqY, sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ) * -α = -(n * α) by ring]; ring
  have hcz : Continuous (fun α => (1 / zz N α) ^ 2) :=
    (continuous_const.div (continuous_zz N) (zz_ne_zero hN)).pow 2
  simp_rw [hpt]
  have hsw : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ n ∈ Fy N H y,
      ((tw N H n : ℝ) : ℂ) * (eL (-(n * α)) * (1 / zz N α) ^ 2)
      = ∑ n ∈ Fy N H y, ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
      ((tw N H n : ℝ) : ℂ) * (eL (-(n * α)) * (1 / zz N α) ^ 2) :=
    intervalIntegral.integral_finset_sum fun n _ => (continuous_const.mul
      (((continuous_e.comp (continuous_const.mul continuous_id).neg)).mul hcz)).intervalIntegrable _ _
  rw [hsw, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (sum_twY_le (y := y) hHN)
  refine sum_le_sum fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with h0 | _
  · have hn' := (mem_filter.mp hn).1
    have hHN' : H = N := by rw [mem_Icc] at hn'; omega
    have htw : tw N H n = 0 := by subst h0; rw [hHN']; unfold tw; simp
    simp [htw]
  have hn1 : 1 ≤ n := by have hn' := (mem_filter.mp hn).1; rw [mem_Icc] at hn'; omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [intervalIntegral.integral_const_mul]
  have hI : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), eL (-(n * α)) * (1 / zz N α) ^ 2
      = ∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine setIntegral_congr_fun measurableSet_Ioc fun α _ => ?_
    rw [e_neg_eq, zz_eq, one_div_pow]
  have h2' := lemma2 hN0 hnr
  rw [hI]
  have e1 : ((tw N H n : ℝ) : ℂ) * (∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
        Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2))
      - ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ)
      = ((tw N H n : ℝ) : ℂ) * ((∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
        Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2))
        - ((n * Real.exp (-n / N) : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tw_nonnegY hHN hn)]
  have hpi : 1 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  calc tw N H n * ‖_‖ ≤ tw N H n * (1 / Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left h2' (tw_nonnegY hHN hn)
    _ ≤ tw N H n * 1 := mul_le_mul_of_nonneg_left hpi (tw_nonnegY hHN hn)
    _ = tw N H n := mul_one _

end LeanLab.LZCesaroShort
