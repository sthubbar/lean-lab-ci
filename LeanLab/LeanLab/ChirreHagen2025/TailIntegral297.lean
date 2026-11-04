import Mathlib

/-!
Integral comparison for P0075 Lemma A.1 part 1, pages 13 and 14.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.TailIntegral297

open MeasureTheory Set

/-- P0075 page 13, the prime summand extended to a real argument. -/
noncomputable def weight (x : ℝ) : ℝ :=
  Real.log x / (Real.sqrt x * (x - 1))

/-- P0075 page 13, nonnegativity of the extended prime summand. -/
theorem weight_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ weight x := by
  unfold weight
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hm : 0 < x - 1 := by linarith
  positivity

/-- P0075 page 13, an integrable majorant for the extended prime summand.
This proves convergence and asserts no numerical tail estimate. -/
theorem weight_le_rpow {x : ℝ} (hx : 2 ≤ x) :
    weight x ≤ 8 * x ^ (-5 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hm : 0 < x - 1 := by linarith
  have hd : 0 < Real.sqrt x * (x - 1) := by positivity
  have hr : 0 < x ^ (5 / 4 : ℝ) := by positivity
  rw [show (-5 / 4 : ℝ) = -(5 / 4) by ring, Real.rpow_neg hx0.le, ← one_div, mul_one_div]
  unfold weight
  rw [div_le_div_iff₀ hd hr]
  have hl := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
  have he : x ^ (1 / 4 : ℝ) * x ^ (5 / 4 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    calc
      x ^ (1 / 4 : ℝ) * x ^ (5 / 4 : ℝ) = x ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_add hx0]; norm_num
      _ = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hx0]; norm_num
      _ = x * x ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
  calc
    Real.log x * x ^ (5 / 4 : ℝ)
        ≤ (x ^ (1 / 4 : ℝ) / (1 / 4)) * x ^ (5 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right hl hr.le
    _ = 4 * (x * Real.sqrt x) := by
      rw [div_eq_mul_inv]; norm_num; nlinarith [he]
    _ ≤ 8 * (Real.sqrt x * (x - 1)) := by
      nlinarith [Real.sqrt_nonneg x]

/-- P0075 page 13, monotonicity used for both tail comparisons. -/
theorem weight_antitone : AntitoneOn weight (Ici (Real.exp 2)) := by
  intro x hx y hy hxy
  have he : (1 : ℝ) < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hx1 : 1 < x := he.trans_le hx
  have hy1 : 1 < y := hx1.trans_le hxy
  have hn : 0 ≤ Real.log x / Real.sqrt x := by
    exact div_nonneg (Real.log_nonneg hx1.le) (Real.sqrt_nonneg _)
  unfold weight
  rw [← div_div, ← div_div]
  exact (div_le_div_of_nonneg_right (Real.log_div_sqrt_antitoneOn hx hy hxy)
      (by linarith : 0 ≤ y - 1)).trans
    (div_le_div_of_nonneg_left hn (by linarith : 0 < x - 1) (by linarith))

/-- P0075 pages 13 and 14, the continuous majorant sampled above the cutoff. -/
noncomputable def tailWeight (x : ℝ) : ℝ := weight (x * Real.log x)

/-- P0075 page 13, a uniform lower threshold for the integral comparison. -/
theorem exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have he : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, pow_two]
  rw [he]
  nlinarith [Real.exp_pos 1]

/-- P0075 page 13, the logarithm is at least one above the chosen threshold. -/
theorem one_le_log {x : ℝ} (hx : 8 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith : 0 < x)]
  linarith [Real.exp_one_lt_d9]

/-- P0075 page 13, the sampled tail is nonnegative. -/
theorem tailWeight_nonneg {x : ℝ} (hx : 8 ≤ x) : 0 ≤ tailWeight x := by
  apply weight_nonneg
  have hl := one_le_log hx
  nlinarith

/-- P0075 page 13, the sampled tail is decreasing. -/
theorem tailWeight_antitone : AntitoneOn tailWeight (Ici 8) := by
  intro x hx y hy hxy
  change 8 ≤ x at hx
  change 8 ≤ y at hy
  have hlx := one_le_log hx
  have hly := one_le_log hy
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  apply weight_antitone
  · exact exp_two_lt_eight.le.trans (by nlinarith)
  · exact exp_two_lt_eight.le.trans (by nlinarith)
  · exact mul_le_mul hxy (Real.log_le_log (by linarith) hxy) (by linarith) hy0

/-- P0075 pages 13 and 14, an integrable majorant for the sampled tail. -/
theorem tailWeight_le_rpow {x : ℝ} (hx : 8 ≤ x) :
    tailWeight x ≤ 8 * x ^ (-5 / 4 : ℝ) := by
  have hl := one_le_log hx
  have hx0 : 0 < x := by linarith
  have hm : x ≤ x * Real.log x := by nlinarith
  exact (weight_le_rpow (by nlinarith : 2 ≤ x * Real.log x)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx0 hm (by norm_num)) (by norm_num))

/-- P0075 page 14, continuity on the tail ray. -/
theorem tailWeight_continuousOn {a : ℝ} (ha : 8 ≤ a) :
    ContinuousOn tailWeight (Ioi a) := by
  intro x hx
  have hx8 : 8 ≤ x := ha.trans hx.le
  have hx0 : 0 < x := by linarith
  have hl := one_le_log hx8
  have hm : 0 < x * Real.log x := by positivity
  have hm1 : x * Real.log x - 1 ≠ 0 := by nlinarith
  unfold tailWeight weight
  apply ContinuousAt.continuousWithinAt
  have hc : ContinuousAt (fun y : ℝ => y * Real.log y) x :=
    continuousAt_id.mul (Real.continuousAt_log hx0.ne')
  exact (hc.log hm.ne').div (hc.sqrt.mul (hc.sub continuousAt_const))
    (mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hm)) hm1)

/-- P0075 page 14, existence of the improper tail integral. -/
theorem tailWeight_integrableOn {a : ℝ} (ha : 8 ≤ a) :
    IntegrableOn tailWeight (Ioi a) := by
  have ha0 : 0 < a := by linarith
  apply ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1) ha0).const_mul 8).mono'
    ((tailWeight_continuousOn ha).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx8 : 8 ≤ x := ha.trans hx.le
  rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg hx8)]
  exact tailWeight_le_rpow hx8

/-- P0075 pages 13 and 14, the integral test for an arbitrary cutoff at least eight. -/
theorem tail_sum_le_integral (N : ℕ) (hN : 8 ≤ N) :
    (∑' n : ℕ, if N < n then tailWeight n else 0) ≤
      ∫ x in Ici (N : ℝ), tailWeight x := by
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : AntitoneOn tailWeight (Ici (N : ℝ)) :=
    tailWeight_antitone.mono (Ici_subset_Ici.mpr hNr)
  have hi := tailWeight_integrableOn hNr
  have hn : ∀ x ∈ Ioi (N : ℝ), 0 ≤ tailWeight x := fun x hx =>
    tailWeight_nonneg (hNr.trans hx.le)
  have hs := ha.summable_of_integrableOn_Ioi hi hn
  have hg : Summable (fun n : ℕ => if N < n then tailWeight n else 0) :=
    by
      convert hs.indicator {n | N < n} using 1
      funext n
      simp [Set.indicator]
  have he := hg.sum_add_tsum_nat_add (N + 1)
  have hz : (∑ n ∈ Finset.range (N + 1), if N < n then tailWeight n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [show ¬ N < n by omega]
  rw [hz, zero_add] at he
  rw [← he, integral_Ici_eq_integral_Ioi]
  simpa only [show ∀ n : ℕ, N < n + (N + 1) by omega, if_pos, Nat.add_assoc] using
    ha.tsum_comp_add_le_integral N hi hn

end LeanLab.ChirreHagen2025.TailIntegral297
