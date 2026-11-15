/-
P0059 Kadiri and Lumley 2014, arXiv 1407.7902v1.
Display 2.62 of Lemma 2.6, the summand C4 times S5 times X^(-1/(R log H)), with S5 of
display 2.44 in the corrected form of Faber and Kadiri, Math. Comp. 87 2018 corrigendum,
which is how `zeroS5` is defined on main. Also displays 2.42 and 2.43 for the signs of
S3 and S4. Evaluated at Table 2 row 43: m = 5, delta = 33490/10^12, sigma = 0.92.
All bounds here are elementary numeric lower bounds, no zero input is used.
AI wrote this Lean code, burst 2026-11-15. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroBounds259

namespace LeanLab.KadiriLumley2014.Route43

open Real
open LeanLab.KadiriLumley2014.Task259

/-- Numeric input for display 2.44: the verified height H = 30610000000 has log at least 24. -/
private lemma log_H_ge : (24 : ℝ) ≤ Real.log 30610000000 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 24 = Real.exp 1 ^ 24 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 24 ≤ (2.7182818286 : ℝ) ^ 24 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 24
    _ ≤ 30610000000 := by norm_num

/-- Numeric input for display 2.62: exp of minus 43 over 24 R, R = 5.69693. -/
private lemma exp_neg_ge : (0.727 : ℝ) ≤ Real.exp (-43 / (5.69693 * 24)) := by
  have h : Real.exp (-43 / (5.69693 * 24)) = Real.exp (-43 / (5.69693 * 24) / 16) ^ 16 := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num
  rw [h]
  have h1 : (1 - 43 / (5.69693 * 24) / 16 : ℝ) ≤ Real.exp (-43 / (5.69693 * 24) / 16) := by
    have := Real.add_one_le_exp (-43 / (5.69693 * 24) / 16 : ℝ)
    linarith
  calc (0.727 : ℝ) ≤ (1 - 43 / (5.69693 * 24) / 16 : ℝ) ^ 16 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 16

/-- Display 2.62 of Lemma 2.6 at Table 2 row 43: the summand C4 times S5 of display 2.44
(corrected form) times X^(-1/(R log H)) is at least 0.035. -/
theorem density_term_ge {δ u X : ℝ} (hδ : δ = 33490 / 10 ^ 12) (hu : u = δ / 5)
    (hXlo : Real.exp 43 / (1 + 1 / 10 ^ 6) ≤ X) (hXhi : X ≤ Real.exp 43) {F : ℝ}
    (hF : 84500 ≤ F) :
    (0.035 : ℝ) ≤ 2 * (Real.exp u + 1) * F / ((Real.exp u - 1) * δ ^ 5) *
      zeroS5 X 5 5.5564 0.4426 (-170070000000) *
        X ^ (-1 / (5.69693 * Real.log 30610000000)) := by
  have hL := log_H_ge
  -- X and log X
  have hX1 : (1 : ℝ) < X := by
    have h44 : (44 : ℝ) ≤ Real.exp 43 := by
      have := Real.add_one_le_exp (43 : ℝ); linarith
    have : (1 : ℝ) < Real.exp 43 / (1 + 1 / 10 ^ 6) := by
      rw [lt_div_iff₀ (by norm_num)]; norm_num; linarith
    linarith
  have hX0 : 0 < X := by linarith
  have hlx0 : 0 < Real.log X := Real.log_pos hX1
  have hlx : Real.log X ≤ 43 := (Real.log_le_iff_le_exp hX0).mpr hXhi
  -- first factor
  have hu' : u = 33490 / 10 ^ 12 / 5 := by rw [hu, hδ]
  have hd0 : 0 < Real.exp u - 1 := by
    have := Real.add_one_lt_exp (x := u) (by rw [hu']; norm_num); linarith
  have hd : Real.exp u - 1 ≤ 6.7e-9 := by
    have := Real.exp_bound_div_one_sub_of_interval (x := u) (by rw [hu']; norm_num)
      (by rw [hu']; norm_num)
    have h2 : 1 / (1 - u) ≤ 1 + 6.7e-9 := by rw [hu']; norm_num
    linarith
  have hG : (1.19e51 : ℝ) ≤ 2 * (Real.exp u + 1) * F / ((Real.exp u - 1) * δ ^ 5) := by
    have hδ5 : 0 < δ ^ 5 := by rw [hδ]; norm_num
    rw [le_div_iff₀ (mul_pos hd0 hδ5)]
    have hc : (1.19e51 : ℝ) * δ ^ 5 ≤ 5.02e13 := by rw [hδ]; norm_num
    have h1 : 1.19e51 * ((Real.exp u - 1) * δ ^ 5) ≤ (Real.exp u - 1) * 5.02e13 := by
      have := mul_le_mul_of_nonneg_left hc hd0.le
      linarith
    have h2 : 2 * (Real.exp u + 1) * 84500 ≤ 2 * (Real.exp u + 1) * F :=
      mul_le_mul_of_nonneg_left hF (by linarith)
    have h3 : (Real.exp u - 1) * 5.02e13 ≤ 6.7e-9 * 5.02e13 :=
      mul_le_mul_of_nonneg_right hd (by norm_num)
    norm_num at h3
    linarith
  -- S5
  have hS : (1.1112 : ℝ) / 30610000000 ^ 5 ≤ zeroS5 X 5 5.5564 0.4426 (-170070000000) := by
    unfold zeroS5
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have hA : (76 : ℝ) ≤ 5.69693 / Real.log X * (Real.log 30610000000) ^ 2 := by
      have h1 : (5.69693 : ℝ) / 43 ≤ 5.69693 / Real.log X :=
        div_le_div_of_nonneg_left (by norm_num) hlx0 hlx
      have h2 : (576 : ℝ) ≤ (Real.log 30610000000) ^ 2 := by nlinarith
      calc (76 : ℝ) ≤ 5.69693 / 43 * 576 := by norm_num
        _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (by positivity)
    have hterm : (5.5564 + 0.4426 / 30610000000 : ℝ) / 5 ≤
        (5.5564 + 0.4426 / 30610000000) * 5.69693 / Real.log X *
          (Real.log 30610000000) ^ 2 /
          ((((5 : ℕ) : ℝ) * 5.69693 / Real.log X) * (Real.log 30610000000) ^ 2 - 1) := by
      have e1 : (5.5564 + 0.4426 / 30610000000 : ℝ) * 5.69693 / Real.log X *
          (Real.log 30610000000) ^ 2 = (5.5564 + 0.4426 / 30610000000) *
            (5.69693 / Real.log X * (Real.log 30610000000) ^ 2) := by ring
      have e2 : (((5 : ℕ) : ℝ) * 5.69693 / Real.log X) * (Real.log 30610000000) ^ 2 - 1 =
          5 * (5.69693 / Real.log X * (Real.log 30610000000) ^ 2) - 1 := by
        push_cast; ring
      rw [e1, e2]
      generalize 5.69693 / Real.log X * (Real.log 30610000000) ^ 2 = A at hA ⊢
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hmid : (0 : ℝ) ≤ 0.4426 * Real.log 30610000000 / 30610000000 := by positivity
    have hc : (0 : ℝ) ≤ 5.5564 + (-170070000000) / 30610000000 := by norm_num
    have hq : (1.1112 : ℝ) ≤ (5.5564 + 0.4426 / 30610000000 : ℝ) / 5 := by norm_num
    linarith
  -- power factor
  have hP : (0.727 : ℝ) ≤ X ^ (-1 / (5.69693 * Real.log 30610000000)) := by
    rw [Real.rpow_def_of_pos hX0]
    refine le_trans exp_neg_ge (Real.exp_le_exp.mpr ?_)
    have hRL : (0 : ℝ) < 5.69693 * Real.log 30610000000 := by positivity
    have h1 : Real.log X / (5.69693 * Real.log 30610000000) ≤ 43 / (5.69693 * 24) :=
      div_le_div₀ (by norm_num) hlx (by norm_num) (by linarith)
    have e : Real.log X * (-1 / (5.69693 * Real.log 30610000000)) =
        -(Real.log X / (5.69693 * Real.log 30610000000)) := by ring
    rw [e]
    have e' : (-43 / (5.69693 * 24) : ℝ) = -(43 / (5.69693 * 24)) := by ring
    rw [e']
    linarith
  calc (0.035 : ℝ) ≤ 1.19e51 * (1.1112 / 30610000000 ^ 5) * 0.727 := by norm_num
    _ ≤ _ := mul_le_mul (mul_le_mul hG hS (by norm_num) (le_trans (by norm_num) hG)) hP
        (by norm_num)
        (mul_nonneg (le_trans (by norm_num) hG) (le_trans (by norm_num) hS))

/-- Display 2.42: S3 at m = 5 is nonnegative, so the B3 summand of display 2.62 may be
dropped in a lower bound. -/
theorem zeroS3_five_nonneg : 0 ≤ zeroS3 5 := by
  unfold zeroS3 countQ countRemainder
  have hL := log_H_ge
  have hpi := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have h2 : (0 : ℝ) < Real.log (30610000000 / (2 * π)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hLL : (0 : ℝ) ≤ Real.log (Real.log 30610000000) :=
    Real.log_nonneg (by linarith)
  have hL0 : (0 : ℝ) < Real.log 30610000000 := by linarith
  have hq : (0 : ℝ) ≤ (0.137 * Real.log 30610000000 + 0.443) /
      (30610000000 * Real.log 30610000000 * Real.log (30610000000 / (2 * π))) := by
    positivity
  have hr : (0 : ℝ) ≤ 0.137 * Real.log 30610000000 +
      0.443 * Real.log (Real.log 30610000000) + 1.588 := by positivity
  have h3 : (0 : ℝ) ≤ (1 + ((5 : ℕ) : ℝ) * Real.log (30610000000 / (2 * π))) /
      (((5 : ℕ) : ℝ) ^ 2 * 30610000000 ^ 5) := by positivity
  have h4 : (0 : ℝ) ≤ 1 / (2 * π) := by positivity
  exact add_nonneg (mul_nonneg (add_nonneg h4 hq) h3)
    (div_nonneg (mul_nonneg (by norm_num) hr) (by norm_num))

/-- Display 2.43: S4 at the Table 2 row 43 coefficients is nonnegative, so its summand of
display 2.62 may be dropped in a lower bound. -/
theorem zeroS4_row_nonneg : 0 ≤ zeroS4 5 5.5564 0.4426 (-170070000000) := by
  unfold zeroS4
  have hL := log_H_ge
  apply div_nonneg _ (by norm_num)
  have h1 : (0 : ℝ) ≤ 0.4426 * Real.log 30610000000 / 30610000000 := by positivity
  have h2 : (0 : ℝ) ≤ 5.5564 * (1 + 1 / ((5 : ℕ) : ℝ)) +
      (-170070000000 + 0.4426 / (((5 : ℕ) : ℝ) + 1)) / 30610000000 := by norm_num
  linarith

end LeanLab.KadiriLumley2014.Route43

#print axioms LeanLab.KadiriLumley2014.Route43.density_term_ge
#print axioms LeanLab.KadiriLumley2014.Route43.zeroS3_five_nonneg
#print axioms LeanLab.KadiriLumley2014.Route43.zeroS4_row_nonneg
