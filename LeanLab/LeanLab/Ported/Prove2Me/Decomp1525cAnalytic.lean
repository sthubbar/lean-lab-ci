/-
Lean Lab analytic completion for task171.
Source: Vaughan 1977 page 96, Lemma 2 and equation 2.16.
https://doi.org/10.1515/crll.1977.290.93
Elementary estimates for deriving equation 2.16 from the cited equation 2.15.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Quadrature

open Real MeasureTheory intervalIntegral
open scoped Classical
open LeanLab.SchnirelmannBounds.Vaughan1977Quadrature

noncomputable section
namespace LeanLab.Ported.Prove2Me.Decomp1525cAnalytic

lemma coarse_theta_error (t : ℝ) (ht : 0 ≤ t) : |Chebyshev.theta t - t| ≤ t := by
  have hl4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_lt_d9]
  have hθ := Chebyshev.theta_le_log4_mul_x ht
  have hθ0 := Chebyshev.theta_nonneg t
  have hp := mul_le_mul_of_nonneg_right hl4.le ht
  rw [abs_le]
  constructor <;> nlinarith


lemma cutoff_facts35 (x : ℝ) (hx : 10 ^ 35 ≤ x) :
    ∃ z : ℝ, 678407 ≤ z ∧ z ≤ x ∧ 80 ≤ Real.log x ∧
      Real.log z = 3 / 4 * Real.log x ∧ 50000 * z * Real.log x ^ 2 ≤ x := by
  have hx0 : 0 < x := by linarith
  set q := Real.exp (Real.log x / 4) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hqx : x = q ^ 4 := by
    rw [hq, ← Real.exp_nat_mul]
    push_cast
    rw [show (4 : ℝ) * (Real.log x / 4) = Real.log x by ring, Real.exp_log hx0]
  have hqQ : 500000000 ≤ q := by
    by_contra h
    have hp := pow_lt_pow_left₀ (lt_of_not_ge h) hq0.le (n := 4) (by norm_num)
    rw [← hqx] at hp
    norm_num at hp
    linarith
  have hlogq : Real.log q = Real.log x / 4 := by rw [hq, Real.log_exp]
  have he2 : Real.exp 2 < 8 := by
    have he : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogQ : Real.log (500000000 : ℝ) ≤ 21 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he : Real.exp 21 = Real.exp 1 ^ 21 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (500000000 : ℝ) ≤ 2.7182818283 ^ 21 := by norm_num
      _ ≤ Real.exp 1 ^ 21 := by gcongr; exact Real.exp_one_gt_d9.le
  have hsQ0 : 0 < Real.sqrt (500000000 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hsQ : 20000 ≤ Real.sqrt (500000000 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 500000000 by norm_num)]
  have hratio := Real.log_div_sqrt_antitoneOn
    (show Real.exp 2 ≤ (500000000 : ℝ) by linarith)
    (show Real.exp 2 ≤ q by linarith) hqQ
  have hratio' : Real.log q / Real.sqrt q ≤ 21 / 20000 := by
    calc Real.log q / Real.sqrt q ≤ Real.log (500000000 : ℝ) / Real.sqrt (500000000 : ℝ) := hratio
      _ ≤ 21 / Real.sqrt (500000000 : ℝ) := div_le_div_of_nonneg_right hlogQ hsQ0.le
      _ ≤ 21 / 20000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsQ
  have hscale : 20000 * Real.log x ≤ 84 * Real.sqrt q := by
    have h := (div_le_div_iff₀ hsq0 (by norm_num : (0 : ℝ) < 20000)).1 hratio'
    rw [hlogq] at h
    linarith
  have hL80 : 80 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have he : Real.exp 80 = Real.exp 1 ^ 80 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc Real.exp 1 ^ 80 ≤ 2.7182818286 ^ 80 := by gcongr; exact Real.exp_one_lt_d9.le
      _ ≤ 10 ^ 35 := by norm_num
      _ ≤ x := hx
  have hscale2 := mul_self_le_mul_self (by nlinarith : (0 : ℝ) ≤ 20000 * Real.log x) hscale
  have hLq : 50000 * Real.log x ^ 2 ≤ q := by
    nlinarith [Real.sq_sqrt hq0.le]
  refine ⟨q ^ 3, ?_, ?_, hL80, ?_, ?_⟩
  · nlinarith [sq_nonneg q, mul_le_mul_of_nonneg_left hqQ (sq_nonneg q)]
  · rw [hqx]
    have : 1 ≤ q := by linarith
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ q ^ 3) (sub_nonneg.2 this)]
  · rw [Real.log_pow, hlogq]
    push_cast
    ring
  · have h := mul_le_mul_of_nonneg_left hLq (by positivity : (0 : ℝ) ≤ q ^ 3)
    calc 50000 * q ^ 3 * Real.log x ^ 2 = q ^ 3 * (50000 * Real.log x ^ 2) := by ring
      _ ≤ q ^ 3 * q := h
      _ = x := by rw [hqx]; ring

lemma pi_li_error_cutoff
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x z : ℝ) (hz : 678407 ≤ z) (hzx : z ≤ x) :
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
      x / (40 * Real.log x ^ 2) + 5 * z + x / (40 * Real.log z ^ 3) := by
  have hx2 : 2 ≤ x := by linarith
  have hz2 : 2 ≤ z := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
    simpa using log_integrable 0 1 (by norm_num : (1 : ℝ) < 2) hx2
  have hi2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x := by
    simpa using log_integrable 0 2 (by norm_num : (1 : ℝ) < 2) hx2
  have hli : (∫ t in (2 : ℝ)..x, 1 / Real.log t) =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    have hd : ∀ t ∈ Set.uIcc (2 : ℝ) x,
        HasDerivAt (fun u : ℝ => u / Real.log u) (1 / Real.log t - 1 / Real.log t ^ 2) t := by
      intro t ht
      rw [Set.uIcc_of_le hx2] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlt : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      convert (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hlt using 1
      · rfl
      · simp only [id]
        field_simp <;> ring
    have h := integral_eq_sub_of_hasDerivAt hd (hi1.sub hi2)
    rw [integral_sub hi1 hi2] at h
    linarith
  let F : ℝ → ℝ := fun t => Chebyshev.theta t / (t * Real.log t ^ 2) - 1 / Real.log t ^ 2
  have hi (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ x) : IntervalIntegrable F volume a b := by
    have hθ : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t ^ 2)) volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
        ((Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set (Set.Icc_subset_Icc ha hb))
    exact hθ.sub (by simpa using log_integrable 0 2 (by linarith : 1 < a) hab)
  have hF (t : ℝ) (ht : 2 ≤ t) : F t = (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
    dsimp [F]
    have ht0 : t ≠ 0 := by linarith
    have hlt : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    field_simp <;> ring
  have he : (Nat.primeCounting ⌊x⌋₊ : ℝ) - (∫ t in (2 : ℝ)..x, 1 / Real.log t) =
      (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, F t := by
    rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2, hli]
    have hθ : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx2).2 (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
    rw [show (∫ t in (2 : ℝ)..x, F t) =
        (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
          ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 from integral_sub hθ hi2]
    ring
  have hsmall : |∫ t in (2 : ℝ)..z, F t| ≤ 4 * (z - 2) := by
    have h := norm_integral_le_of_norm_le_const (a := (2 : ℝ)) (b := z) (C := 4) (f := F) (by
      intro t ht
      rw [Set.uIoc_of_le hz2] at ht
      have ht2 : 2 ≤ t := ht.1.le
      have ht0 : 0 < t := by linarith
      have hlt : 0 < Real.log t := Real.log_pos (by linarith)
      have hlt2 : (1 / 2 : ℝ) ≤ Real.log t := by
        have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht2
        linarith [Real.log_two_gt_d9]
      rw [Real.norm_eq_abs, hF t ht2, abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 2), div_le_iff₀ (by positivity)]
      have hsq : 1 ≤ 4 * Real.log t ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hsq ht0.le
      nlinarith [coarse_theta_error t ht0.le])
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ z - 2)] using h
  have htail : |∫ t in z..x, F t| ≤ (1 / (40 * Real.log z ^ 3)) * (x - z) := by
    have h := norm_integral_le_of_norm_le_const (a := z) (b := x)
        (C := 1 / (40 * Real.log z ^ 3)) (f := F) (by
      intro t ht
      rw [Set.uIoc_of_le hzx] at ht
      have ht2 : 2 ≤ t := by linarith [ht.1]
      have ht0 : 0 < t := by linarith
      have hlt : 0 < Real.log t := Real.log_pos (by linarith)
      have hzt : Real.log z ≤ Real.log t := Real.log_le_log (by linarith) ht.1.le
      rw [Real.norm_eq_abs, hF t ht2, abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 2)]
      calc |Chebyshev.theta t - t| / (t * Real.log t ^ 2)
          ≤ (t / (40 * Real.log t)) / (t * Real.log t ^ 2) :=
            div_le_div_of_nonneg_right (h215 t (by linarith [ht.1])).le (by positivity)
        _ = 1 / (40 * Real.log t ^ 3) := by field_simp <;> ring
        _ ≤ 1 / (40 * Real.log z ^ 3) := by gcongr)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hzx)] using h
  have hend : |(Chebyshev.theta x - x) / Real.log x| ≤ x / (40 * Real.log x ^ 2) := by
    rw [abs_div, abs_of_pos hlx]
    calc |Chebyshev.theta x - x| / Real.log x ≤ (x / (40 * Real.log x)) / Real.log x :=
        div_le_div_of_nonneg_right (h215 x (by linarith)).le hlx.le
      _ = _ := by field_simp <;> ring
  have hc : |(2 : ℝ) / Real.log 2| ≤ 4 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    linarith [Real.log_two_gt_d9]
  rw [he, ← integral_add_adjacent_intervals (hi 2 z le_rfl hz2 hzx) (hi z x hz2 hzx le_rfl)]
  have hnorm := abs_add_le ((Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2)
    ((∫ t in (2 : ℝ)..z, F t) + ∫ t in z..x, F t)
  have hnorm1 := abs_add_le ((Chebyshev.theta x - x) / Real.log x) (2 / Real.log 2)
  have hnorm2 := abs_add_le (∫ t in (2 : ℝ)..z, F t) (∫ t in z..x, F t)
  have htail' : (1 / (40 * Real.log z ^ 3)) * (x - z) ≤ x / (40 * Real.log z ^ 3) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

lemma eq216_of_eq215
    (h215 : LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.Eq215) :
    LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.Eq216 := by
  intro x hx
  obtain ⟨z, hz, hzx, hL80, hlz, hhead⟩ := cutoff_facts35 x hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hlz0 : 0 < Real.log z := by rw [hlz]; positivity
  have h := pi_li_error_cutoff h215 x z hz hzx
  set v := x / Real.log x ^ 2 with hv
  have hv0 : 0 < v := by positivity
  have hhead' : 5 * z ≤ v / 10000 := by
    rw [hv, div_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hd : Real.log x ^ 2 * 1000 ≤ 40 * (3 / 4 * Real.log x) ^ 3 := by
    have hprod := mul_nonneg (sq_nonneg (Real.log x)) (show 0 ≤ Real.log x - 80 by linarith)
    nlinarith
  have htail : x / (40 * Real.log z ^ 3) ≤ v / 1000 := by
    rw [hlz, hv, div_div]
    exact div_le_div_of_nonneg_left hx0.le (by positivity) hd
  have e40 : x / (40 * Real.log x ^ 2) = v / 40 := by rw [hv]; field_simp
  have e38 : x / (38 * Real.log x ^ 2) = v / 38 := by rw [hv]; field_simp
  change |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| < _
  rw [e38]
  rw [e40] at h
  linarith

lemma coarse_bound_exceeds_budget (x : ℝ) (hx : 10 ^ 35 ≤ x) :
    x / (40 * Real.log x) < x := by
  obtain ⟨_, _, _, hL, _, _⟩ := cutoff_facts35 x hx
  exact div_lt_self (by linarith) (by linarith)

end LeanLab.Ported.Prove2Me.Decomp1525cAnalytic
