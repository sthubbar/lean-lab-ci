/-
P0059 Kadiri and Lumley 2014, arXiv 1407.7902v1.
Page 3 equation 2.7, the Brun Titchmarsh tail, and page 9 display 2.64 with the
weight of page 9 equation 3.1, evaluated at Table 2 row 1, threshold 4 * 10^18:
m = 5, delta = 35800 / 10^12, u = delta / 5, a = 0.2130, X just below 4 * 10^18.
The last summand of the envelope budget is bounded BELOW by 0.1128 here.
AI wrote this Lean code, burst 2026-11-15. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.WeightTail

namespace LeanLab.KadiriLumley2014.Route0
open Real intervalIntegral LeanLab.KadiriLumley2014.Task64

/-- Page 9 equation 3.1 with m = 5: the primitive of the polynomial weight on zero to x. -/
private lemma weight5_integral (x : ℝ) :
    (∫ t in (0 : ℝ)..x, weight 5 t) =
      1024 * (x ^ 6 / 6 - 5 * x ^ 7 / 7 + 5 * x ^ 8 / 4 - 10 * x ^ 9 / 9 + x ^ 10 / 2
        - x ^ 11 / 11) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun y : ℝ => 1024 * (y ^ 6 / 6 - 5 * y ^ 7 / 7 + 5 * y ^ 8 / 4
        - 10 * y ^ 9 / 9 + y ^ 10 / 2 - y ^ 11 / 11)) (weight 5 t) t := by
    intro t _
    have h := ((((((hasDerivAt_pow 6 t).div_const 6).sub
      (((hasDerivAt_pow 7 t).const_mul 5).div_const 7)).add
      (((hasDerivAt_pow 8 t).const_mul 5).div_const 4)).sub
      (((hasDerivAt_pow 9 t).const_mul 10).div_const 9)).add
      ((hasDerivAt_pow 10 t).div_const 2)).sub
      ((hasDerivAt_pow 11 t).div_const 11)
    convert h.const_mul 1024 using 1
    unfold weight
    norm_num
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((weight_continuous 5).intervalIntegrable _ _)
  rw [h]
  norm_num

/-- Page 9 display 2.64: the normalized endpoint mass nu at m = 5 and a = 0.2130. -/
private lemma tail_ratio_ge :
    (0.03183 : ℝ) ≤ tailMass 5 (2129 / 10000 + 1 / 10000) / (∫ t in (0 : ℝ)..1, weight 5 t) := by
  rw [tailMass_eq_two, weight5_integral, weight5_integral]
  norm_num

/-- An enclosure of log 5 from the series of log (1 - x) at x = 1 / 5. -/
private lemma log_5_bounds : 160943 / 100000 ≤ Real.log 5 ∧ Real.log 5 ≤ 160944 / 100000 := by
  have e : (5 : ℝ) = 2 ^ 2 / (1 - 1 / 5) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 5) (by norm_num) 10
  rw [abs_le] at h
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_two_gt_d9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The logarithm of the Table 2 threshold 4 * 10^18 = 2^20 * 5^18. -/
private lemma log_x0_bounds :
    (428326 / 10000 : ℝ) ≤ Real.log (4 * 10 ^ 18) ∧ Real.log (4 * 10 ^ 18) ≤ 428329 / 10000 := by
  have e : (4 * 10 ^ 18 : ℝ) = 2 ^ 20 * 5 ^ 18 := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  obtain ⟨h1, h2⟩ := log_5_bounds
  have h3 := Real.log_two_lt_d9
  have h4 := Real.log_two_gt_d9
  norm_num
  constructor <;> linarith

/-- The scalar e^u - 1 of page 3 equation 2.7 at row 1 is at most exp(-18.7). -/
private lemma expm1_le {u : ℝ} (hu : u = 35800 / 10 ^ 12 / 5) :
    Real.exp u - 1 ≤ Real.exp (-(187 / 10 : ℝ)) := by
  have h1 : 1 - u ≤ Real.exp (-u) := by
    have := Real.add_one_le_exp (-u)
    linarith
  have hupos : (0 : ℝ) < 1 - u := by rw [hu]; norm_num
  have h2 : Real.exp u ≤ 1 / (1 - u) := by
    rw [Real.exp_neg] at h1
    have hepos := Real.exp_pos u
    rw [le_div_iff₀ hupos]
    have := mul_le_mul_of_nonneg_left h1 hepos.le
    rw [mul_inv_cancel₀ hepos.ne'] at this
    linarith
  have h3 : Real.exp u - 1 ≤ 72 / 10 ^ 10 := by
    have : 1 / (1 - u) ≤ 1 + 72 / 10 ^ 10 := by
      rw [div_le_iff₀ hupos, hu]; norm_num
    linarith
  have he : Real.exp 1 < 2.71829 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 := Real.exp_pos 1
  have h07 : Real.exp (7 / 10 : ℝ) < 2.02 := by
    have h4 : Real.exp (7 / 10 : ℝ) ^ 10 = Real.exp 1 ^ 7 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h5 : Real.exp 1 ^ 7 < (2.02 : ℝ) ^ 10 :=
      lt_of_lt_of_le (pow_lt_pow_left₀ he he0.le (by norm_num)) (by norm_num)
    rw [← h4] at h5
    exact lt_of_pow_lt_pow_left₀ 10 (by norm_num) h5
  have h18 : Real.exp (18 : ℝ) ≤ (2.71829 : ℝ) ^ 18 := by
    have : Real.exp (18 : ℝ) = Real.exp 1 ^ 18 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ he0.le he.le 18
  have hbig : Real.exp (187 / 10 : ℝ) ≤ 10 ^ 10 / 72 := by
    have : Real.exp (187 / 10 : ℝ) = Real.exp 18 * Real.exp (7 / 10) := by
      rw [← Real.exp_add]; norm_num
    rw [this]
    calc Real.exp 18 * Real.exp (7 / 10) ≤ (2.71829 : ℝ) ^ 18 * 2.02 :=
          mul_le_mul h18 h07.le (Real.exp_pos _).le (by positivity)
      _ ≤ 10 ^ 10 / 72 := by norm_num
  have hneg : (72 : ℝ) / 10 ^ 10 ≤ Real.exp (-(187 / 10 : ℝ)) := by
    rw [Real.exp_neg]
    have hp := Real.exp_pos (187 / 10 : ℝ)
    rw [le_inv_comm₀ (by norm_num) hp]
    calc Real.exp (187 / 10 : ℝ) ≤ 10 ^ 10 / 72 := hbig
      _ = (72 / 10 ^ 10 : ℝ)⁻¹ := by norm_num
  linarith

/-- Paper page 3 equation 2.7 and page 9 display 2.64 at Table 2 row 1, threshold
4 * 10^18: the Brun Titchmarsh tail summand of the envelope budget is at least 0.1128
when X is within a factor 1 + 10^-6 below 4 * 10^18. -/
theorem tail_term_ge {δ u X : ℝ} (hδ : δ = 35800 / 10 ^ 12) (hu : u = δ / 5)
    (hXlo : 4 * 10 ^ 18 / (1 + 1 / 10 ^ 6) ≤ X) (hXhi : X ≤ 4 * 10 ^ 18) :
    (0.1128 : ℝ) ≤ (2 * (1 + δ) * tailMass 5 (2129 / 10000 + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight 5 t)) *
      (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1))) := by
  have hu' : u = 35800 / 10 ^ 12 / 5 := by rw [hu, hδ]
  have hu0 : 0 < u := by rw [hu']; norm_num
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hx0 : (0 : ℝ) < 4 * 10 ^ 18 := by norm_num
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hXlo
  have hE0 : 0 < Real.exp u - 1 := by linarith [Real.add_one_lt_exp hu0.ne']
  obtain ⟨hL1, hL2⟩ := log_x0_bounds
  have hlogX_lo : 428326 / 10000 - 1 / 10 ^ 6 ≤ Real.log X := by
    have h1 : Real.log (4 * 10 ^ 18 / (1 + 1 / 10 ^ 6)) ≤ Real.log X :=
      Real.log_le_log (by positivity) hXlo
    rw [Real.log_div hx0.ne' (by norm_num)] at h1
    have h2 : Real.log (1 + 1 / 10 ^ 6 : ℝ) ≤ 1 / 10 ^ 6 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 10 ^ 6)
      linarith
    linarith
  have hlogX_hi : Real.log X ≤ 428329 / 10000 :=
    (Real.log_le_log hX0 hXhi).trans hL2
  have hnum : 428326 / 10000 - 1 / 10 ^ 6 ≤ Real.log (Real.exp u * X * (1 + δ)) := by
    have h1 : X ≤ Real.exp u * X * (1 + δ) := by
      have hexp : 1 ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
      have : X ≤ Real.exp u * X := le_mul_of_one_le_left hX0.le hexp
      exact this.trans (le_mul_of_one_le_right (by positivity) (by linarith))
    exact hlogX_lo.trans (Real.log_le_log hX0 h1)
  have hden_hi : Real.log (X * (Real.exp u - 1)) ≤ 428329 / 10000 - 187 / 10 := by
    rw [Real.log_mul hX0.ne' hE0.ne']
    have h1 : Real.log (Real.exp u - 1) ≤ -(187 / 10 : ℝ) := by
      have := Real.log_le_log hE0 (expm1_le hu')
      rwa [Real.log_exp] at this
    linarith
  have hden_pos : 0 < Real.log (X * (Real.exp u - 1)) := by
    apply Real.log_pos
    have hXbig : (10 : ℝ) ^ 12 ≤ X := le_trans (by norm_num) hXlo
    have hEu : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
    calc (1 : ℝ) < 10 ^ 12 * u := by rw [hu']; norm_num
      _ ≤ X * (Real.exp u - 1) := mul_le_mul hXbig hEu hu0.le hX0.le
  have hratio : (428326 / 10000 - 1 / 10 ^ 6) / (428329 / 10000 - 187 / 10 : ℝ) ≤
      Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)) := by
    rw [div_le_div_iff₀ (by norm_num) hden_pos]
    calc (428326 / 10000 - 1 / 10 ^ 6 : ℝ) * Real.log (X * (Real.exp u - 1))
        ≤ (428326 / 10000 - 1 / 10 ^ 6) * (428329 / 10000 - 187 / 10) :=
          mul_le_mul_of_nonneg_left hden_hi (by norm_num)
      _ ≤ Real.log (Real.exp u * X * (1 + δ)) * (428329 / 10000 - 187 / 10) :=
          mul_le_mul_of_nonneg_right hnum (by norm_num)
  have hcoef : (2 * 0.03183 : ℝ) ≤ 2 * (1 + δ) * tailMass 5 (2129 / 10000 + 1 / 10000) /
      (∫ t in (0 : ℝ)..1, weight 5 t) := by
    have hr := tail_ratio_ge
    have hr0 : (0 : ℝ) ≤ tailMass 5 (2129 / 10000 + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight 5 t) := le_trans (by norm_num) hr
    rw [mul_div_assoc]
    calc (2 * 0.03183 : ℝ) ≤ 2 * (tailMass 5 (2129 / 10000 + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight 5 t)) := by linarith
      _ ≤ 2 * (1 + δ) * (tailMass 5 (2129 / 10000 + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight 5 t)) :=
          mul_le_mul_of_nonneg_right (by linarith) hr0
  calc (0.1128 : ℝ) ≤ (2 * 0.03183) *
        ((428326 / 10000 - 1 / 10 ^ 6) / (428329 / 10000 - 187 / 10)) := by norm_num
    _ ≤ _ := mul_le_mul hcoef hratio (by norm_num) (le_trans (by norm_num) hcoef)

end LeanLab.KadiriLumley2014.Route0

#print axioms LeanLab.KadiriLumley2014.Route0.tail_term_ge
