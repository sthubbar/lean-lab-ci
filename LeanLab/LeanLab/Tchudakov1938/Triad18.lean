import Mathlib
import LeanLab.Tchudakov1938.Deduction

namespace LeanLab.Tchudakov1938.Triad18
open Real Finset

lemma exp_le_three : Real.exp 1 ≤ 3 := by
  have := Real.exp_one_lt_d9
  linarith

lemma exp2_le_ten : Real.exp 2 ≤ 10 := by
  have h1 : Real.exp 1 ≤ 3 := exp_le_three
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 : 0 ≤ Real.exp 1 := Real.exp_pos 1 |>.le
  nlinarith

lemma triad18_mono_deriv (x : ℝ) (hx6 : 6 ≤ x) :
    0 ≤ Real.log x - 2 * (x - 5) / x := by
  have hl : (1 : ℝ) ≤ Real.log x := by
    have : (2 : ℝ) < 6 := by norm_num
    have : Real.exp 1 < 6 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have : 1 < Real.log 6 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr this
    exact this.le.trans (Real.log_le_log (by norm_num) hx6)
  have heq : Real.log x - 2 * (x - 5) / x = Real.log x - 2 + 10 / x := by
    have : x ≠ 0 := by linarith
    calc Real.log x - 2 * (x - 5) / x
      _ = Real.log x - (2 * x - 10) / x := by ring
      _ = Real.log x - (2 * x / x - 10 / x) := by rw [sub_div]
      _ = Real.log x - (2 - 10 / x) := by rw [mul_div_cancel_right₀ 2 this]
      _ = Real.log x - 2 + 10 / x := by ring
  rw [heq]
  by_cases h10 : x ≤ 10
  · have h10x : 1 ≤ 10 / x := (one_le_div (by positivity)).mpr h10
    linarith
  · have hn10 : 10 < x := not_le.mp h10
    have hl10 : 2 ≤ Real.log 10 := by
      have hlt : Real.exp 2 ≤ 10 := exp2_le_ten
      exact (Real.le_log_iff_exp_le (by norm_num)).mpr hlt
    have hl' : 2 ≤ Real.log x := hl10.trans (Real.log_le_log (by norm_num) hn10.le)
    have h10x : 0 ≤ 10 / x := by positivity
    linarith

lemma triad18_deriv (x : ℝ) (hx : 0 < x) (hlx : Real.log x ≠ 0) :
    HasDerivAt (fun t => (t - 5) / (Real.log t ^ 2)) ((Real.log x - 2 * (x - 5) / x) / (Real.log x ^ 3)) x := by
  have hd1 : HasDerivAt (fun t => t - 5) 1 x := by
    apply HasDerivAt.sub_const
    exact hasDerivAt_id x
  have hd2 : HasDerivAt (fun t => Real.log t ^ 2) (2 * Real.log x * x⁻¹) x := by
    have hd_log := hasDerivAt_log (ne_of_gt hx)
    have hd_sq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * Real.log x) (Real.log x) := by
      have := hasDerivAt_pow 2 (Real.log x)
      push_cast at this
      simp only [pow_one] at this
      exact this
    exact HasDerivAt.comp x hd_sq hd_log
  have hdiv := HasDerivAt.div hd1 hd2 (pow_ne_zero 2 hlx)
  have heq : (1 * Real.log x ^ 2 - (x - 5) * (2 * Real.log x * x⁻¹)) / (Real.log x ^ 2) ^ 2 =
      ((Real.log x - 2 * (x - 5) / x) / (Real.log x ^ 3)) := by
    have h3 : (Real.log x ^ 2) ^ 2 = Real.log x ^ 3 * Real.log x := by ring
    rw [h3, div_eq_div_iff]
    · ring
    · have : Real.log x ^ 3 * Real.log x = Real.log x ^ 4 := by ring
      rw [this]
      exact pow_ne_zero 4 hlx
    · exact pow_ne_zero 3 hlx
  rwa [heq] at hdiv

lemma triad18_mono (x y : ℝ) (hx6 : 6 ≤ x) (hxy : x ≤ y) :
    (x - 5) / Real.log x ^ 2 ≤ (y - 5) / Real.log y ^ 2 := by
  have H : MonotoneOn (fun t => (t - 5) / (Real.log t ^ 2)) (Set.Ici 6) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 6)
    · have h_cont1 : ContinuousOn (fun t : ℝ => t - 5) (Set.Ici 6) := continuousOn_id.sub continuousOn_const
      have h_cont2 : ContinuousOn (fun t : ℝ => Real.log t ^ 2) (Set.Ici 6) := by
        have hc_log : ContinuousOn Real.log (Set.Ici 6) := by
          apply ContinuousOn.mono continuousOn_log
          intro t ht
          have : 0 < t := by linarith [show 6 ≤ t from ht]
          exact ne_of_gt this
        exact ContinuousOn.pow hc_log 2
      apply ContinuousOn.div h_cont1 h_cont2
      intro t ht
      have ht6 : 6 ≤ t := ht
      have hlt0 : 0 < Real.log t := by
        have h : Real.log 6 ≤ Real.log t := Real.log_le_log (by norm_num) ht6
        have h' : 0 < Real.log 6 := Real.log_pos (by norm_num)
        linarith
      exact ne_of_gt (pow_pos hlt0 2)
    · intro t ht
      rw [interior_Ici] at ht
      have ht6 : 6 < t := ht
      have ht0 : 0 < t := by linarith
      have hlt0 : Real.log t ≠ 0 := by
        have h : Real.log 6 < Real.log t := Real.log_lt_log (by norm_num) ht6
        have h' : 0 < Real.log 6 := Real.log_pos (by norm_num)
        linarith
      exact (triad18_deriv t ht0 hlt0).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht6 : 6 < t := ht
      have ht0 : 0 < t := by linarith
      have hlt0 : 0 < Real.log t := by
        have h : Real.log 6 < Real.log t := Real.log_lt_log (by norm_num) ht6
        have h' : 0 < Real.log 6 := Real.log_pos (by norm_num)
        linarith
      have h1 : 0 ≤ Real.log t - 2 * (t - 5) / t := triad18_mono_deriv t ht6.le
      have h2 : 0 < Real.log t ^ 3 := pow_pos hlt0 3
      exact div_nonneg h1 h2.le
  exact H (Set.mem_Ici.mpr hx6) (Set.mem_Ici.mpr (hx6.trans hxy)) hxy

theorem triad18_main (m n : ℕ) (h6 : 6 ≤ n) (hnm : n ≤ m) :
    (1 / 6 : ℝ) * n / Real.log n ^ 2 ≤ ∑ a ∈ Finset.Icc 3 (m - 3), 1 / (Real.log a * Real.log (m - a : ℕ)) := by
  have H : ((n : ℝ) - 5) / Real.log (n : ℝ) ^ 2 ≤ ((m : ℝ) - 5) / Real.log (m : ℝ) ^ 2 := by
    apply triad18_mono (n : ℝ) (m : ℝ)
    · exact_mod_cast h6
    · exact_mod_cast hnm
  have h1 : (1 / 6 : ℝ) * n ≤ (n : ℝ) - 5 := by
    calc (1 / 6 : ℝ) * n
      _ ≤ (1 / 6 : ℝ) * n + 5 / 6 * n - 5 := by
        have : (5 : ℝ) ≤ 5 / 6 * n := by
          calc (5 : ℝ) = 5 / 6 * 6 := by norm_num
            _ ≤ 5 / 6 * n := mul_le_mul_of_nonneg_left (by exact_mod_cast h6) (by norm_num)
        linarith
      _ = (n : ℝ) - 5 := by ring
  have h2 : 0 < Real.log (n : ℝ) ^ 2 := by
    have hn : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact pow_pos (Real.log_pos hn) 2
  have H' : (1 / 6 : ℝ) * n / Real.log n ^ 2 ≤ ((n : ℝ) - 5) / Real.log (n : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have hm6 : 6 ≤ m := by omega
  have H_lem := LeanLab.Tchudakov1938.lemma2_first m hm6
  exact H'.trans (H.trans H_lem)

end LeanLab.Tchudakov1938.Triad18
