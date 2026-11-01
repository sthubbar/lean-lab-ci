/-
AI wrote the Lean code. Binary Goldbach is OPEN.
Task163 isolates the elementary steps of Lemma 6 i on pages 56 and 57.
Task202 isolates two cited analytic source leaves. Both remain open.
The original theta and prime-counting leaves are conditional assemblies.
No unconditional proof of a cited theta input is claimed.
-/
import LeanLab.RieselVaughan1983.Lemma8
import LeanLab.RieselVaughan1983.Lemma6Theta
import LeanLab.Common.ThetaWindowDusart
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Chebyshev MeasureTheory Set

namespace LeanLab.RieselVaughan1983


namespace Task163

open LeanLab.Common.ThetaWindow Lemma6Theta

/-- The cited Dusart threshold leaves a gap at the start of equation 4.5. -/
theorem dusart_threshold_gap : exp (22 : ℝ) < 7713133853 := by
  have h := pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos (1 : ℝ)).le (by decide : (22 : ℕ) ≠ 0)
  rw [exp_one_pow] at h
  norm_num at h ⊢
  linarith

/-- The lab's coarse 1.11 square-root term already exceeds the page 56 gap budget at exp 22. -/
theorem coarse_gap_at_22_too_large :
    3961 / 10000000 * exp (22 : ℝ) / 22 < 1.11 * exp 11 := by
  have he11 : exp (11 : ℝ) < 60000 := by
    have h := pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos (1 : ℝ)).le (by decide : (11 : ℕ) ≠ 0)
    rw [exp_one_pow] at h
    norm_num at h ⊢
    linarith
  have he22 : exp (22 : ℝ) = exp 11 * exp 11 := by rw [← exp_add]; norm_num
  rw [he22]
  have hp := exp_pos (11 : ℝ)
  nlinarith [mul_pos hp (sub_pos.mpr he11)]

/-- The elementary Mathlib Chebyshev lower estimate does not reach equation 4.5. -/
theorem chebyshev_lower_is_insufficient (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ log x) :
    (x - 1) * log 2 - log (x + 2) - 2 * sqrt x * log x <
      x - 862 / 100000 * x / log x := by
  have hL0 : 0 < log x := by linarith
  have hx1 : 1 < x := (log_pos_iff hx0.le).mp hL0
  have hlog2 : log (2 : ℝ) ≤ 0.7 := by linarith [log_two_lt_d9]
  have hmain := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ x - 1 by linarith)
  have hlog : 0 ≤ log (x + 2) := log_nonneg (by linarith)
  have hroot : 0 ≤ 2 * sqrt x * log x := by positivity
  have hcoarse : (x - 1) * log 2 - log (x + 2) - 2 * sqrt x * log x ≤ 0.7 * x := by
    linarith
  have herror : 862 / 100000 * x / log x < 0.3 * x := by
    apply (div_lt_iff₀ hL0).2
    have hp := mul_pos hx0 (show 0 < 0.3 * log x - 862 / 100000 by linarith)
    nlinarith
  exact hcoarse.trans_lt (by linarith)

/-- The logarithmic range log x at least 23 is above the cited Dusart threshold. -/
theorem dusart_threshold_23 : (7713133853 : ℝ) ≤ exp 23 := by
  have h := exp_nat_ge 23
  norm_num at h ⊢
  linarith

/-- Page 56 equation 4.5 from the cited Dusart input above its threshold. -/
theorem theta_lower_of_dusart (hD : DusartThm52k2) (x : ℝ)
    (hx : 7713133853 ≤ x) (hL : 22 ≤ log x) :
    x - 862 / 100000 * x / log x < θ x := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < log x := by linarith
  have he := (abs_le.mp (hD x hx)).1
  have hsmall : 0.01 * x / log x ^ 2 < 862 / 100000 * x / log x := by
    apply (div_lt_div_iff₀ (by positivity : 0 < log x ^ 2) hL0).2
    have hmul : 0 < x * log x := mul_pos hx0 hL0
    have hc : 0.01 < (862 / 100000 : ℝ) * log x := by linarith
    nlinarith [mul_pos hmul (sub_pos.mpr hc)]
  linarith

/-- Page 56 equation 4.5 from the two explicit errors quoted immediately above it. -/
theorem theta_lower_of_psi (x : ℝ) (hx0 : 0 < x) (hL : 22 ≤ log x)
    (hpsi : |ψ x - x| ≤ 822 / 100000 * x / log x)
    (hgap : ψ x - θ x ≤ 3961 / 10000000 * x / log x) :
    x - 862 / 100000 * x / log x < θ x := by
  have hpos : 0 < x / log x := div_pos hx0 (by linarith)
  have he := (abs_le.mp hpsi).1
  have hmargin : (822 / 100000 : ℝ) * x / log x +
      3961 / 10000000 * x / log x < 862 / 100000 * x / log x := by
    calc
      _ = ((822 / 100000 : ℝ) + 3961 / 10000000) * (x / log x) := by ring
      _ < (862 / 100000 : ℝ) * (x / log x) :=
        mul_lt_mul_of_pos_right (by norm_num) hpos
      _ = _ := by ring
  linarith

/-- Page 56 conversion of the quoted Rosser and Schoenfeld gap into its numerical budget. -/
theorem rs_gap_budget (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ log x) :
    1.001102 * sqrt x + 3 * x ^ (1 / 3 : ℝ) < 3961 / 10000000 * x / log x := by
  have hL0 : 0 < log x := by linarith
  have he11 : (59874 : ℝ) ≤ exp 11 := by
    have h := exp_nat_ge 11
    norm_num at h ⊢
    linarith
  have he14 : (1202604 : ℝ) ≤ exp 14 := by
    have h := exp_nat_ge 14
    norm_num at h ⊢
    linarith
  have he23 : (473 / 243 : ℝ) ≤ exp (2 / 3) := by
    have h := sum_le_exp_of_nonneg (x := (2 / 3 : ℝ)) (by norm_num) 5
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  have he443 : (2340000 : ℝ) ≤ exp (44 / 3) := by
    rw [show (44 / 3 : ℝ) = 14 + 2 / 3 by ring, exp_add]
    have h := mul_le_mul he14 he23 (by norm_num) (exp_pos (14 : ℝ)).le
    norm_num at h ⊢
    linarith
  have hyx : exp 22 ≤ x := (le_log_iff_exp_le hx0).mp hx
  have hhalf : log x / sqrt x ≤ 22 / 59874 := by
    have h := log_div_sqrt_antitoneOn
      (show exp 22 ∈ Ici (exp 2) from exp_le_exp.mpr (by norm_num))
      (show x ∈ Ici (exp 2) from (exp_le_exp.mpr (by norm_num : (2 : ℝ) ≤ 22)).trans hyx) hyx
    have hs : sqrt (exp (22 : ℝ)) = exp 11 := by
      rw [sqrt_eq_rpow, ← exp_mul]
      norm_num
    dsimp only at h
    rw [log_exp, hs] at h
    exact h.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) he11)
  have htwo : log x / x ^ (2 / 3 : ℝ) ≤ 22 / 2340000 := by
    have h := log_div_self_rpow_antitoneOn (a := (2 / 3 : ℝ)) (by norm_num)
      (show exp 22 ∈ Ici (exp (2 / 3 : ℝ)⁻¹) from exp_le_exp.mpr (by norm_num))
      (show x ∈ Ici (exp (2 / 3 : ℝ)⁻¹) from
        (exp_le_exp.mpr (by norm_num : (2 / 3 : ℝ)⁻¹ ≤ 22)).trans hyx) hyx
    dsimp only at h
    rw [log_exp, ← exp_mul] at h
    norm_num only [show (22 : ℝ) * (2 / 3) = 44 / 3 by ring] at h
    exact h.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) he443)
  have hfirst : log x * sqrt x ≤ (22 / 59874 : ℝ) * x := by
    have h := (div_le_iff₀ (sqrt_pos.mpr hx0)).mp hhalf
    calc
      _ ≤ ((22 / 59874 : ℝ) * sqrt x) * sqrt x :=
        mul_le_mul_of_nonneg_right h (sqrt_nonneg _)
      _ = _ := by rw [mul_assoc, mul_self_sqrt hx0.le]
  have hsecond : log x * x ^ (1 / 3 : ℝ) ≤ (22 / 2340000 : ℝ) * x := by
    have h := (div_le_iff₀ (rpow_pos_of_pos hx0 (2 / 3 : ℝ))).mp htwo
    calc
      _ ≤ ((22 / 2340000 : ℝ) * x ^ (2 / 3 : ℝ)) * x ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right h (rpow_nonneg hx0.le _)
      _ = _ := by rw [mul_assoc, ← rpow_add hx0]; norm_num
  apply (lt_div_iff₀ hL0).2
  have hconstant : ((1.001102 : ℝ) * (22 / 59874) + 3 * (22 / 2340000)) * x <
      (3961 / 10000000 : ℝ) * x := mul_lt_mul_of_pos_right (by norm_num) hx0
  nlinarith

/-- Page 56 equation 4.5 with only the quoted analytic psi and gap bounds as inputs. -/
theorem theta_lower_of_psi_and_rs_gap (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ log x)
    (hpsi : |ψ x - x| ≤ 822 / 100000 * x / log x)
    (hgap : ψ x - θ x ≤ 1.001102 * sqrt x + 3 * x ^ (1 / 3 : ℝ)) :
    x - 862 / 100000 * x / log x < θ x := by
  exact theta_lower_of_psi x hx0 hx hpsi (hgap.trans (rs_gap_budget x hx0 hx).le)

/-- Equation 4.5 from exactly the three analytic bounds quoted on page 56. -/
theorem theta_lower_of_paper_inputs
    (h43 : ∀ t : ℝ, 0 < t → 3000 ≤ log t →
      |θ t - t| ≤ 154 / 1000000 * t / log t)
    (h44 : ∀ t : ℝ, 0 < t → 22 ≤ log t → log t ≤ 5000 →
      |ψ t - t| ≤ 822 / 100000 * t / log t)
    (hRS6 : ∀ t : ℝ, 0 < t →
      ψ t - θ t ≤ 1.001102 * sqrt t + 3 * t ^ (1 / 3 : ℝ))
    (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ log x) :
    x - 862 / 100000 * x / log x < θ x := by
  by_cases hx3000 : 3000 ≤ log x
  · have h := (abs_le.mp (h43 x hx0 hx3000)).1
    have hp : 0 < x / log x := div_pos hx0 (by linarith)
    have hm : 154 / 1000000 * x / log x < 862 / 100000 * x / log x := by
      calc
        _ = (154 / 1000000 : ℝ) * (x / log x) := by ring
        _ < (862 / 100000 : ℝ) * (x / log x) :=
          mul_lt_mul_of_pos_right (by norm_num) hp
        _ = _ := by ring
    linarith
  · exact theta_lower_of_psi_and_rs_gap x hx0 hx
      (h44 x hx0 hx (by linarith)) (hRS6 x hx0)

/-- Dusart 2010 Theorem 5.2 k = 1 covers the whole range of equation 4.5. -/
theorem theta_lower_of_dusart_k1
    (hD : ∀ t : ℝ, 908994923 ≤ t → |θ t - t| ≤ 1 / 1000 * t / log t)
    (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ log x) :
    x - 862 / 100000 * x / log x < θ x := by
  have he22 : (908994923 : ℝ) ≤ exp 22 := by
    have h := exp_nat_ge 22
    norm_num at h ⊢
    linarith
  have hx22 : exp 22 ≤ x := (le_log_iff_exp_le hx0).mp hx
  have h := (abs_le.mp (hD x (he22.trans hx22))).1
  have hp : 0 < x / log x := div_pos hx0 (by linarith)
  have hm : 1 / 1000 * x / log x < 862 / 100000 * x / log x := by
    calc
      _ = (1 / 1000 : ℝ) * (x / log x) := by ring
      _ < (862 / 100000 : ℝ) * (x / log x) :=
        mul_lt_mul_of_pos_right (by norm_num) hp
      _ = _ := by ring
  linarith

/-- Page 56 lower integral using the primitive t divided by log squared t. -/
theorem tail_lower_4_5
    (hθ : ∀ t : ℝ, exp 22 ≤ t → t - 862 / 100000 * t / log t ≤ θ t)
    {x : ℝ} (hx : exp 22 ≤ x) :
    Gprim 0 x - Gprim 0 (exp 22) ≤ ∫ t in exp 22..x, θ t / (t * log t ^ 2) := by
  have hy : 1 < exp (22 : ℝ) := (one_lt_exp_iff).2 (by norm_num)
  refine intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hx
    (Gprim_continuousOn _ hy)
    (fun t ht ↦ (hasDerivAt_Gprim _ (by linarith [ht.1])).hasDerivWithinAt)
    (theta_integrableOn x (by linarith [add_one_le_exp (22 : ℝ)]) le_rfl)
    (fun t ht ↦ ?_)
  have ht0 : 0 < t := by linarith [ht.1, exp_pos (22 : ℝ)]
  have hL : 22 ≤ log t := by
    rw [← log_exp (22 : ℝ)]
    exact log_le_log (exp_pos _) ht.1.le
  have hL0 : 0 < log t := by linarith
  have hdiff : Gprim' 0 t ≤ (t - 862 / 100000 * t / log t) / (t * log t ^ 2) := by
    unfold Gprim'
    field_simp
    nlinarith [sq_nonneg (log t)]
  exact hdiff.trans (div_le_div_of_nonneg_right (hθ t ht.1.le) (by positivity))

/-- Page 56 endpoint loss at y = exp 22 for log x at least 32. -/
theorem endpoint_loss_32 (x : ℝ) (hx0 : 0 < x) (hx : 32 ≤ log x) :
    Gprim 0 (exp 22) ≤ (x / log x ^ 2) / 10000 := by
  have hL0 : 0 < log x := by linarith
  have hmono := sq_mul_exp_le (L0 := 32) (L := log x) (by norm_num) hx
  have he10 : (22000 : ℝ) ≤ exp 10 := by
    have h := exp_nat_ge 10
    norm_num at h ⊢
    linarith
  have he32 : exp (32 : ℝ) = exp 22 * exp 10 := by rw [← exp_add]; norm_num
  rw [exp_log hx0, he32] at hmono
  unfold Gprim
  rw [log_exp]
  simp only [zero_mul, zero_div, add_zero]
  rw [le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity : 0 < log x ^ 2)]
  norm_num only [show (22 : ℝ) ^ 2 = 484 by norm_num]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 484)]
  have hprod : log x ^ 2 * exp 22 * 22000 ≤ log x ^ 2 * (exp 22 * exp 10) := by
    nlinarith [mul_nonneg (sq_nonneg (log x)) (exp_pos (22 : ℝ)).le]
  nlinarith

/-- Equation 4.1 above exp 32, conditional only on equation 4.5. -/
theorem integral_32_of_theta
    (hθ : ∀ t : ℝ, exp 22 ≤ t → t - 862 / 100000 * t / log t ≤ θ t)
    (x : ℝ) (hx0 : 0 < x) (hx : 32 ≤ log x) :
    x / log x + 9911 / 10000 * x / log x ^ 2 < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hL0 : 0 < log x := by linarith
  have hyx : exp 22 ≤ x := by
    rw [← exp_log hx0]
    exact exp_le_exp.2 (by linarith)
  have h2y : (2 : ℝ) ≤ exp 22 := by linarith [add_one_le_exp (22 : ℝ)]
  rw [pi_split h2y hyx]
  have hhead := head_nonneg h2y
  have htail := tail_lower_4_5 hθ hyx
  have hend := endpoint_loss_32 x hx0 hx
  have hterm : x / log x - 862 / 100000 * x / log x ^ 2 ≤ θ x / log x := by
    apply (le_div_iff₀ hL0).2
    convert hθ x hyx using 1; field_simp
  have hG : Gprim 0 x = x / log x ^ 2 := by simp [Gprim]
  rw [hG] at htail
  set B := x / log x ^ 2 with hB
  have hBpos : 0 < B := by positivity
  have hterm' : x / log x - (862 / 100000 : ℝ) * B ≤ θ x / log x := by
    simpa only [hB, mul_div_assoc] using hterm
  have hresult : x / log x + (9911 / 10000 : ℝ) * B <
      θ x / log x + (∫ t in (2 : ℝ)..exp 22, θ t / (t * log t ^ 2)) +
        ∫ t in exp 22..x, θ t / (t * log t ^ 2) := by
    linarith
  simpa only [hB, mul_div_assoc] using hresult

/-- Page 57 proves the stronger coefficient 1 on the finite logarithmic range. -/
theorem integral_17_35_of_rs (hRS : RS1975Cor2Thm7)
    (x : ℝ) (hx0 : 0 < x) (hx1 : 17 ≤ log x) (hx2 : log x ≤ 35) :
    x / log x + x / log x ^ 2 < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  set L := log x with hL
  have hxe : x = exp L := (exp_log hx0).symm
  have hL0 : 0 < L := by linarith
  have hyx : exp 13.5 ≤ x := by rw [hxe]; exact exp_le_exp.2 (by linarith)
  have hy := exp_13_5
  have h2y : (2 : ℝ) ≤ exp 13.5 := by linarith
  rw [pi_split h2y hyx, ← hL]
  have hI1 := head_nonneg h2y
  have hI2 := tail_lower hRS hy hyx
  have hGy : Gprim 1.975 (exp 13.5) ≤ 0.00629 * exp 13.5 := by
    unfold Gprim
    rw [log_exp]
    have hp := exp_pos (13.5 : ℝ)
    have hid : exp 13.5 / 13.5 ^ 2 + 1.975 * exp 13.5 / 13.5 ^ 3 =
        (1 / 13.5 ^ 2 + 1.975 / 13.5 ^ 3) * exp 13.5 := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right (by norm_num) hp.le
  set B := x / L ^ 2 with hB
  set C := x / L ^ 3 with hC
  have hBpos : 0 < B := by positivity
  have hCpos : 0 < C := by positivity
  have hGx : Gprim 1.975 x = B + 1.975 * C := by unfold Gprim; rw [← hL, hB, hC]; ring
  rw [hGx] at hI2
  have hCL : C * L = B := by rw [hC, hB]; field_simp
  have hθ := hRS x (by linarith)
  have hθL : x / L - B / 40 ≤ θ x / L := by
    rw [le_div_iff₀ hL0]
    have hid : (x / L - B / 40) * L = x - x / (40 * L) := by rw [hB]; field_simp
    linarith
  rcases le_or_gt L 20 with h20 | h20
  · have hCB : B / 20 ≤ C := by
      have : B ≤ C * 20 := by rw [← hCL]; exact mul_le_mul_of_nonneg_left h20 hCpos.le
      linarith
    have hmono := sq_mul_exp_le (L0 := 17) (L := L) (by norm_num) hx1
    have hsplit : exp (17 : ℝ) = exp 13.5 * exp 3.5 := by rw [← exp_add]; norm_num
    rw [hsplit, ← hxe] at hmono
    have h35 := exp_3_5
    have hyB : exp 13.5 ≤ 8.87 * B := by
      rw [hB, ← mul_div_assoc, le_div_iff₀ (by positivity)]
      have hp := exp_pos (13.5 : ℝ)
      nlinarith
    nlinarith
  · have hCB : B / 35 ≤ C := by
      have : B ≤ C * 35 := by rw [← hCL]; exact mul_le_mul_of_nonneg_left hx2 hCpos.le
      linarith
    have hmono := sq_mul_exp_le (L0 := 20) (L := L) (by norm_num) h20.le
    have hsplit : exp (20 : ℝ) = exp 13.5 * exp 6.5 := by rw [← exp_add]; norm_num
    rw [hsplit, ← hxe] at hmono
    have he65 : (650 : ℝ) ≤ exp 6.5 := by
      have h := exp_add_half 6
      norm_num at h ⊢
      linarith
    have hyB : exp 13.5 ≤ 0.62 * B := by
      rw [hB, ← mul_div_assoc, le_div_iff₀ (by positivity)]
      have hp := exp_pos (13.5 : ℝ)
      nlinarith
    nlinarith

/-- The full page 55 Lemma 6 i from precisely the two page 56 and 57 theta inputs. -/
theorem lemma6i_of_theta_and_rs
    (hθ : ∀ t : ℝ, exp 22 ≤ t → t - 862 / 100000 * t / log t ≤ θ t)
    (hRS : RS1975Cor2Thm7) : Lemma6i := by
  intro x hx0 hx17
  by_cases hx32 : 32 ≤ log x
  · exact integral_32_of_theta hθ x hx0 hx32
  · have hx35 : log x ≤ 35 := by linarith
    have h := integral_17_35_of_rs hRS x hx0 hx17 hx35
    have hb : 0 < x / log x ^ 2 := by positivity
    have hs : 9911 / 10000 * x / log x ^ 2 < x / log x ^ 2 := by
      calc
        _ = (9911 / 10000 : ℝ) * (x / log x ^ 2) := by ring
        _ < 1 * (x / log x ^ 2) := mul_lt_mul_of_pos_right (by norm_num) hb
        _ = _ := one_mul _
    linarith

end Task163

namespace Task202

/-- LEAF. Dusart 2010 page 4 Theorem 5.2, k = 1, eta = 0.001.
Source: https://arxiv.org/abs/1002.0442v1.
CITED analytic input. Unproved here. Consumers are CONDITIONAL ON this leaf. -/
theorem dusart2010_theta_k1 (x : ℝ) (hx : 908994923 ≤ x) :
    |θ x - x| < 1 / 1000 * x / log x := by
  sorry

/-- LEAF. Riesel and Vaughan 1983 page 57, first display, quoting Rosser
and Schoenfeld 1975 Corollary 2 to Theorem 7.
Only the bounded initial interval below the Dusart threshold is left open.
Source: https://doi.org/10.1007/BF02384300, page 57.
CITED analytic input. Unproved here. Consumers are CONDITIONAL ON this leaf. -/
theorem rs1975_theta_lower_initial (x : ℝ) (hx : 678407 ≤ x)
    (hxD : x < 908994923) :
    x - x / (40 * log x) < θ x := by
  sorry

/-- The cited Rosser and Schoenfeld input reduces to a bounded initial interval.
CONDITIONAL ON the supplied Dusart bound and initial theta bound. -/
theorem rs1975_of_dusart_k1_and_initial
    (hD : ∀ t : ℝ, 908994923 ≤ t → |θ t - t| ≤ 1 / 1000 * t / log t)
    (hinit : ∀ t : ℝ, 678407 ≤ t → t < 908994923 →
      t - t / (40 * log t) ≤ θ t) : Lemma6Theta.RS1975Cor2Thm7 := by
  intro t ht
  by_cases htD : 908994923 ≤ t
  · have ht0 : 0 < t := by linarith
    have hlog : 0 < log t := log_pos (by linarith)
    have hsmall : 1 / 1000 * t / log t < t / (40 * log t) := by
      rw [div_mul_eq_div_div, div_lt_div_iff_of_pos_right hlog]
      linarith
    have htheta := (abs_le.mp (hD t htD)).1
    linarith
  · exact hinit t ht (lt_of_not_ge htD)

/-- Lemma 6 i from two explicit analytic inputs, without using either open leaf.
CONDITIONAL ON the supplied Dusart and Rosser and Schoenfeld inputs. -/
theorem lemma6i_of_dusart_k1_and_initial
    (hD : ∀ t : ℝ, 908994923 ≤ t → |θ t - t| ≤ 1 / 1000 * t / log t)
    (hinit : ∀ t : ℝ, 678407 ≤ t → t < 908994923 →
      t - t / (40 * log t) ≤ θ t) : Lemma6i := by
  refine Task163.lemma6i_of_theta_and_rs ?_ (rs1975_of_dusart_k1_and_initial hD hinit)
  intro t ht
  have ht0 : 0 < t := (exp_pos (22 : ℝ)).trans_le ht
  have hL : 22 ≤ log t := by
    rw [← log_exp (22 : ℝ)]
    exact log_le_log (exp_pos _) ht
  exact (Task163.theta_lower_of_dusart_k1 hD t ht0 hL).le

/-- Page 56 monotonicity of X to power 11/4 times exp minus X.
The proof uses the logarithm tangent inequality from Mathlib. -/
theorem rs1975_decay_le (a X : ℝ) (ha : (11 / 4 : ℝ) ≤ a) (hX : a ≤ X) :
    X ^ (11 / 4 : ℝ) * exp (-X) ≤ a ^ (11 / 4 : ℝ) * exp (-a) := by
  have ha0 : 0 < a := by linarith
  have hX0 : 0 < X := ha0.trans_le hX
  have hlog0 : 0 ≤ log X - log a := sub_nonneg.mpr (log_le_log ha0 hX)
  have hlog : log X - log a ≤ X / a - 1 := by
    simpa only [log_div hX0.ne' ha0.ne'] using
      log_le_sub_one_of_pos (div_pos hX0 ha0)
  have hm := mul_le_mul_of_nonneg_right hlog ha0.le
  simp only [sub_mul, div_mul_cancel₀ _ ha0.ne', one_mul] at hm
  have hp := mul_le_mul_of_nonneg_right ha hlog0
  rw [rpow_def_of_pos hX0, rpow_def_of_pos ha0, ← exp_add, ← exp_add]
  apply exp_le_exp.mpr
  linarith

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- Page 56 numerical reduction of the explicit error formula on page 55.
The rational cutoff 17.635 lies below `sqrt (3000 / R)`. -/
theorem rs1975_error_budget (X : ℝ) (hX : 3527 / 200 ≤ X) :
    (257634 / 1000000 : ℝ) * (9645908801 / 1000000000) *
      (1 + (96642 / 100000 : ℝ) / X) * X ^ (11 / 4 : ℝ) * exp (-X) <
        154 / 1000000 := by
  have hpow : (3527 / 200 : ℝ) ^ (11 / 4 : ℝ) ≤ 5353 / 2 := by
    apply (rpow_le_rpow_iff (rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3527 / 200) _)
      (by norm_num) (by norm_num : (0 : ℝ) < 4)).mp
    rw [← rpow_mul (by norm_num : (0 : ℝ) ≤ 3527 / 200)]
    norm_num
  have he : (45570000 : ℝ) ≤ exp (3527 / 200) := by
    have h := sum_le_exp_of_nonneg (x := (3527 / 200 : ℝ)) (by norm_num) 35
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hend : (3527 / 200 : ℝ) ^ (11 / 4 : ℝ) * exp (-(3527 / 200)) ≤
      (5353 / 2 : ℝ) / 45570000 := by
    calc
      _ = (3527 / 200 : ℝ) ^ (11 / 4 : ℝ) / exp (3527 / 200) := by
        simp only [exp_neg, div_eq_mul_inv]
      _ ≤ (5353 / 2 : ℝ) / exp (3527 / 200) :=
        div_le_div_of_nonneg_right hpow (exp_pos _).le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
  have hg := (rs1975_decay_le (3527 / 200) X (by norm_num) hX).trans hend
  have hq : 1 + (96642 / 100000 : ℝ) / X ≤
      1 + (96642 / 100000 : ℝ) / (3527 / 200) := by
    have h := div_le_div_of_nonneg_left
      (by norm_num : (0 : ℝ) ≤ 96642 / 100000)
      (by norm_num : (0 : ℝ) < 3527 / 200) hX
    linarith only [h]
  calc
    _ = ((257634 / 1000000 : ℝ) * (9645908801 / 1000000000)) *
        (1 + (96642 / 100000 : ℝ) / X) * (X ^ (11 / 4 : ℝ) * exp (-X)) := by ring
    _ ≤ ((257634 / 1000000 : ℝ) * (9645908801 / 1000000000)) *
        (1 + (96642 / 100000 : ℝ) / (3527 / 200)) *
          (X ^ (11 / 4 : ℝ) * exp (-X)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) (by positivity)
    _ ≤ ((257634 / 1000000 : ℝ) * (9645908801 / 1000000000)) *
        (1 + (96642 / 100000 : ℝ) / (3527 / 200)) * ((5353 / 2 : ℝ) / 45570000) :=
      mul_le_mul_of_nonneg_left hg (by norm_num)
    _ < _ := by norm_num

/-- Page 56 equation 4.3 from the explicit Theorem 2 error quoted on page 55.
CONDITIONAL ON the pointwise Rosser and Schoenfeld analytic error input. -/
theorem theta_error_4_3_of_rs1975 (x : ℝ) (hx0 : 0 < x) (hx : 3000 ≤ log x)
    (hRS : |θ x - x| ≤ x * ((257634 / 1000000 : ℝ) *
      (1 + (96642 / 100000 : ℝ) / sqrt (log x / (9645908801 / 1000000000))) *
      (sqrt (log x / (9645908801 / 1000000000))) ^ (3 / 4 : ℝ) *
      exp (-sqrt (log x / (9645908801 / 1000000000))))) :
    |θ x - x| < 154 / 1000000 * x / log x := by
  have hL0 : 0 < log x := by linarith
  set X := sqrt (log x / (9645908801 / 1000000000))
  change |θ x - x| ≤ x * ((257634 / 1000000 : ℝ) *
    (1 + (96642 / 100000 : ℝ) / X) * X ^ (3 / 4 : ℝ) * exp (-X)) at hRS
  have hX0 : 0 < X := by
    dsimp only [X]
    exact sqrt_pos.mpr (div_pos hL0 (by norm_num))
  have hXX : X ^ 2 = log x / (9645908801 / 1000000000) := by
    dsimp only [X]
    exact sq_sqrt (div_nonneg hL0.le (by norm_num))
  have hX : (3527 / 200 : ℝ) ≤ X := by
    by_contra! h
    have hs := pow_lt_pow_left₀ h hX0.le (by decide : (2 : ℕ) ≠ 0)
    nlinarith only [hs, hXX, hx]
  have hLid : log x = (9645908801 / 1000000000 : ℝ) * X ^ 2 := by
    nlinarith only [hXX]
  have hp : X ^ (3 / 4 : ℝ) * X ^ 2 = X ^ (11 / 4 : ℝ) := by
    rw [← rpow_natCast X 2, ← rpow_add hX0]
    norm_num
  have hbudget : (257634 / 1000000 : ℝ) * (1 + (96642 / 100000 : ℝ) / X) *
      X ^ (3 / 4 : ℝ) * exp (-X) * log x < 154 / 1000000 := by
    calc
      _ = (257634 / 1000000 : ℝ) * (9645908801 / 1000000000) *
          (1 + (96642 / 100000 : ℝ) / X) * X ^ (11 / 4 : ℝ) * exp (-X) := by
        rw [hLid, ← hp]
        ring
      _ < _ := rs1975_error_budget X hX
  have heps : (257634 / 1000000 : ℝ) * (1 + (96642 / 100000 : ℝ) / X) *
      X ^ (3 / 4 : ℝ) * exp (-X) < (154 / 1000000 : ℝ) / log x :=
    (lt_div_iff₀ hL0).2 hbudget
  calc
    _ ≤ x * ((257634 / 1000000 : ℝ) * (1 + (96642 / 100000 : ℝ) / X) *
        X ^ (3 / 4 : ℝ) * exp (-X)) := hRS
    _ < x * ((154 / 1000000 : ℝ) / log x) := mul_lt_mul_of_pos_left heps hx0
    _ = _ := by ring

/-- Lemma 6 i from the four original analytic inputs quoted on pages 55 to 57.
CONDITIONAL ON Rosser and Schoenfeld Theorem 2, its psi table bound,
the 1962 Theorem 6 gap and the 1975 Corollary 2 to Theorem 7 lower bound. -/
theorem lemma6i_of_original_rs_inputs
    (hRS2 : ∀ t : ℝ, 0 < t → 105 ≤ log t →
      |θ t - t| ≤ t * ((257634 / 1000000 : ℝ) *
        (1 + (96642 / 100000 : ℝ) / sqrt (log t / (9645908801 / 1000000000))) *
        (sqrt (log t / (9645908801 / 1000000000))) ^ (3 / 4 : ℝ) *
        exp (-sqrt (log t / (9645908801 / 1000000000)))))
    (h44 : ∀ t : ℝ, 0 < t → 22 ≤ log t → log t ≤ 5000 →
      |ψ t - t| ≤ 822 / 100000 * t / log t)
    (h62 : ∀ t : ℝ, 0 < t →
      ψ t - θ t ≤ 1.001102 * sqrt t + 3 * t ^ (1 / 3 : ℝ))
    (hRS7 : Lemma6Theta.RS1975Cor2Thm7) : Lemma6i := by
  refine Task163.lemma6i_of_theta_and_rs ?_ hRS7
  intro t ht
  have ht0 : 0 < t := (exp_pos (22 : ℝ)).trans_le ht
  have hL : 22 ≤ log t := by
    rw [← log_exp (22 : ℝ)]
    exact log_le_log (exp_pos _) ht
  exact (Task163.theta_lower_of_paper_inputs
    (fun u hu0 huL ↦ (theta_error_4_3_of_rs1975 u hu0 huL
      (hRS2 u hu0 (by linarith))).le) h44 h62 t ht0 hL).le

end Task202

/-- LEAF. Page 56, (4.5): θ(x) > x - 0.00862 x / log x for log x >= 22. -/
theorem theta_lower_bound_4_5 (x : ℝ) (hx0 : 0 < x) (hx : 22 ≤ Real.log x) :
    x - 862 / 100000 * x / Real.log x < θ x := by
  -- CONDITIONAL ON Task202.dusart2010_theta_k1.
  exact Task163.theta_lower_of_dusart_k1
    (fun t ht ↦ (Task202.dusart2010_theta_k1 t ht).le) x hx0 hx

/-- LEAF. Page 56, integral bound leading to (4.1) for log x >= 32. -/
theorem lemma6i_integral_32 (x : ℝ) (hx0 : 0 < x) (hx : 32 ≤ Real.log x) :
    x / Real.log x + 9911 / 10000 * x / Real.log x ^ 2 < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  -- CONDITIONAL ON Task202.dusart2010_theta_k1 through equation 4.5.
  refine Task163.integral_32_of_theta ?_ x hx0 hx
  intro t ht
  have ht0 : 0 < t := (exp_pos (22 : ℝ)).trans_le ht
  have hlog : 22 ≤ log t := by
    rw [← log_exp (22 : ℝ)]
    exact log_le_log (exp_pos _) ht
  exact (theta_lower_bound_4_5 t ht0 hlog).le

/-- LEAF. Page 57, Rosser-Schoenfeld corollary bound for log x between 17 and 35. -/
theorem lemma6i_integral_17_35 (x : ℝ) (hx0 : 0 < x) (hx1 : 17 ≤ Real.log x) (hx2 : Real.log x ≤ 35) :
    x / Real.log x + 9911 / 10000 * x / Real.log x ^ 2 < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  -- CONDITIONAL ON the two Task202 analytic source leaves.
  have hRS : Lemma6Theta.RS1975Cor2Thm7 :=
    Task202.rs1975_of_dusart_k1_and_initial
      (fun t ht ↦ (Task202.dusart2010_theta_k1 t ht).le)
      (fun t ht htD ↦ (Task202.rs1975_theta_lower_initial t ht htD).le)
  have h := Task163.integral_17_35_of_rs hRS x hx0 hx1 hx2
  have hB : 0 < x / log x ^ 2 := div_pos hx0 (sq_pos_of_pos (by linarith))
  have hsmall : (9911 / 10000 : ℝ) * (x / log x ^ 2) < x / log x ^ 2 := by
    exact (mul_lt_mul_of_pos_right (by norm_num : (9911 / 10000 : ℝ) < 1) hB).trans_eq
      (one_mul _)
  rw [mul_div_assoc]
  linarith

/-- The exact cited statement of Lemma 6 (i). -/
theorem lemma6i_decomposed : Lemma6i := by
  intro x hx0 hx17
  by_cases hx32 : 32 ≤ Real.log x
  · exact lemma6i_integral_32 x hx0 hx32
  · push Not at hx32
    exact lemma6i_integral_17_35 x hx0 hx17 (hx32.le.trans (by norm_num))

end LeanLab.RieselVaughan1983
