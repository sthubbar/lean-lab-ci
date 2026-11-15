/-
P0059 Kadiri and Lumley 2014, arXiv 1407.7902v1.
Page 3 equation 2.7, the Brun Titchmarsh tail, and page 9 display 2.64 with the
weight of page 9 equation 3.1, evaluated at Table 2 row 43:
m = 5, delta = 33490 / 10^12, u = delta / 5, a = 0.2148, X near e^43.
The last summand of the envelope budget is bounded BELOW by 0.1175 here.
AI wrote this Lean code, burst 2026-11-15. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.WeightTail

namespace LeanLab.KadiriLumley2014.Route43
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

/-- Page 9 display 2.64: the normalized endpoint mass nu at m = 5 and a = 0.2148. -/
private lemma tail_ratio_ge :
    (0.03317 : ℝ) ≤ tailMass 5 (2147 / 10000 + 1 / 10000) / (∫ t in (0 : ℝ)..1, weight 5 t) := by
  rw [tailMass_eq_two, weight5_integral, weight5_integral]
  norm_num

/-- The scalar e^u - 1 of page 3 equation 2.7 at row 43 is at most exp(-18.75). -/
private lemma expm1_le {u : ℝ} (hu : u = 33490 / 10 ^ 12 / 5) :
    Real.exp u - 1 ≤ Real.exp (-(75 / 4 : ℝ)) := by
  -- exp u ≤ 1 / (1 - u)
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
  have h3 : Real.exp u - 1 ≤ 68 / 10 ^ 10 := by
    have : 1 / (1 - u) ≤ 1 + 68 / 10 ^ 10 := by
      rw [div_le_iff₀ hupos, hu]; norm_num
    linarith
  -- exp (75 / 4) ≤ 10 ^ 10 / 68
  have he : Real.exp 1 < 2.71829 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 := Real.exp_pos 1
  have h34 : Real.exp (3 / 4 : ℝ) < 2.12 := by
    have h4 : Real.exp (3 / 4 : ℝ) ^ 4 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h5 : Real.exp 1 ^ 3 < (2.12 : ℝ) ^ 4 :=
      lt_of_lt_of_le (pow_lt_pow_left₀ he he0.le (by norm_num)) (by norm_num)
    rw [← h4] at h5
    exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) h5
  have h18 : Real.exp (18 : ℝ) ≤ (2.71829 : ℝ) ^ 18 := by
    have : Real.exp (18 : ℝ) = Real.exp 1 ^ 18 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ he0.le he.le 18
  have hbig : Real.exp (75 / 4 : ℝ) ≤ 10 ^ 10 / 68 := by
    have : Real.exp (75 / 4 : ℝ) = Real.exp 18 * Real.exp (3 / 4) := by
      rw [← Real.exp_add]; norm_num
    rw [this]
    calc Real.exp 18 * Real.exp (3 / 4) ≤ (2.71829 : ℝ) ^ 18 * 2.12 :=
          mul_le_mul h18 h34.le (Real.exp_pos _).le (by positivity)
      _ ≤ 10 ^ 10 / 68 := by norm_num
  have hneg : (68 : ℝ) / 10 ^ 10 ≤ Real.exp (-(75 / 4 : ℝ)) := by
    rw [Real.exp_neg]
    have hp := Real.exp_pos (75 / 4 : ℝ)
    rw [le_inv_comm₀ (by norm_num) hp]
    calc Real.exp (75 / 4 : ℝ) ≤ 10 ^ 10 / 68 := hbig
      _ = (68 / 10 ^ 10 : ℝ)⁻¹ := by norm_num
  linarith

/-- Paper page 3 equation 2.7 and page 9 display 2.64 at Table 2 row 43: the Brun
Titchmarsh tail summand of the envelope budget is at least 0.1175 when X is within a
factor 1 + 10^-6 below e^43. -/
theorem tail_term_ge {δ u X : ℝ} (hδ : δ = 33490 / 10 ^ 12) (hu : u = δ / 5)
    (hXlo : Real.exp 43 / (1 + 1 / 10 ^ 6) ≤ X) (hXhi : X ≤ Real.exp 43) :
    (0.1175 : ℝ) ≤ (2 * (1 + δ) * tailMass 5 (2147 / 10000 + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight 5 t)) *
      (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1))) := by
  have hu' : u = 33490 / 10 ^ 12 / 5 := by rw [hu, hδ]
  have hu0 : 0 < u := by rw [hu']; norm_num
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have he43 : (0 : ℝ) < Real.exp 43 := Real.exp_pos _
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hXlo
  have hE0 : 0 < Real.exp u - 1 := by linarith [Real.add_one_lt_exp hu0.ne']
  -- lower bound for log X
  have hlogX_lo : 43 - 1 / 10 ^ 6 ≤ Real.log X := by
    have h1 : Real.log (Real.exp 43 / (1 + 1 / 10 ^ 6)) ≤ Real.log X :=
      Real.log_le_log (by positivity) hXlo
    rw [Real.log_div he43.ne' (by norm_num), Real.log_exp] at h1
    have h2 : Real.log (1 + 1 / 10 ^ 6 : ℝ) ≤ 1 / 10 ^ 6 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 10 ^ 6)
      linarith
    linarith
  have hlogX_hi : Real.log X ≤ 43 := by
    have := Real.log_le_log hX0 hXhi
    rwa [Real.log_exp] at this
  -- numerator
  have hnum : 43 - 1 / 10 ^ 6 ≤ Real.log (Real.exp u * X * (1 + δ)) := by
    have h1 : X ≤ Real.exp u * X * (1 + δ) := by
      have hexp : 1 ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
      have : X ≤ Real.exp u * X := le_mul_of_one_le_left hX0.le hexp
      exact this.trans (le_mul_of_one_le_right (by positivity) (by linarith))
    exact hlogX_lo.trans (Real.log_le_log hX0 h1)
  -- denominator
  have hden_hi : Real.log (X * (Real.exp u - 1)) ≤ 97 / 4 := by
    rw [Real.log_mul hX0.ne' hE0.ne']
    have h1 : Real.log (Real.exp u - 1) ≤ -(75 / 4 : ℝ) := by
      have := Real.log_le_log hE0 (expm1_le hu')
      rwa [Real.log_exp] at this
    linarith
  have hden_pos : 0 < Real.log (X * (Real.exp u - 1)) := by
    apply Real.log_pos
    have h2 : (2 : ℝ) ^ 43 ≤ Real.exp 43 := by
      have h43 : Real.exp (43 : ℝ) = Real.exp 1 ^ 43 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h43]
      exact pow_le_pow_left₀ (by norm_num)
        (le_trans (by norm_num) Real.exp_one_gt_d9.le) 43
    have hXbig : (10 : ℝ) ^ 12 ≤ X := by
      refine le_trans ?_ hXlo
      rw [le_div_iff₀ (by norm_num)]
      exact le_trans (by norm_num) h2
    have hEu : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
    calc (1 : ℝ) < 10 ^ 12 * u := by rw [hu']; norm_num
      _ ≤ X * (Real.exp u - 1) := mul_le_mul hXbig hEu hu0.le hX0.le
  have hratio : (43 - 1 / 10 ^ 6) / (97 / 4 : ℝ) ≤
      Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)) := by
    rw [div_le_div_iff₀ (by norm_num) hden_pos]
    calc (43 - 1 / 10 ^ 6 : ℝ) * Real.log (X * (Real.exp u - 1))
        ≤ (43 - 1 / 10 ^ 6) * (97 / 4) :=
          mul_le_mul_of_nonneg_left hden_hi (by norm_num)
      _ ≤ Real.log (Real.exp u * X * (1 + δ)) * (97 / 4) :=
          mul_le_mul_of_nonneg_right hnum (by norm_num)
  have hcoef : (2 * 0.03317 : ℝ) ≤ 2 * (1 + δ) * tailMass 5 (2147 / 10000 + 1 / 10000) /
      (∫ t in (0 : ℝ)..1, weight 5 t) := by
    have hr := tail_ratio_ge
    have hr0 : (0 : ℝ) ≤ tailMass 5 (2147 / 10000 + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight 5 t) := le_trans (by norm_num) hr
    rw [mul_div_assoc]
    calc (2 * 0.03317 : ℝ) ≤ 2 * (tailMass 5 (2147 / 10000 + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight 5 t)) := by linarith
      _ ≤ 2 * (1 + δ) * (tailMass 5 (2147 / 10000 + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight 5 t)) :=
          mul_le_mul_of_nonneg_right (by linarith) hr0
  calc (0.1175 : ℝ) ≤ (2 * 0.03317) * ((43 - 1 / 10 ^ 6) / (97 / 4)) := by norm_num
    _ ≤ _ := mul_le_mul hcoef hratio (by norm_num) (le_trans (by norm_num) hcoef)

end LeanLab.KadiriLumley2014.Route43

#print axioms LeanLab.KadiriLumley2014.Route43.tail_term_ge
