import Mathlib
import LeanLab.PNTPort.ExplicitPsi1.PsiSchoenfeld
import LeanLab.ChirreHagen2025.Bilinear

/-!
# Chirre-Hagen's `ThetaRel` from the lab's own explicit RH bound for `ψ`

I-5260, unit U-6702, CLOUD 20261020T1816Z-cloud48, track T2. AI wrote this file. Known
mathematics: an RH bound of Schoenfeld's shape for `ψ`, crude in the constants.

Under RH, CONDITIONAL ON the Hasanalizade-Shen-Wong zero counts `HSWN70`, `HSWHead14` and on
`Ordinates14`, all for the true ordinates `gZ`:
* `psi_sub_le_rh`, `sub_psi_le_rh`: `|ψ(x) - x| ≤ 2 x / 10^6` for `x ≥ 10^16`, from
  `psi_upper_gen` and `psi_lower_gen` with `h = x / 10^6` and `T = 10^5`;
* `psi_sub_theta_le_small`: `ψ(x) - θ(x) ≤ 76 x / 10^8` for `x ≥ 10^16`, from Mathlib;
* `abs_theta_sub_le_rh`: `|θ(u) - u| ≤ 3 u / 10^6` for `u ≥ 10^16`;
* `thetaRel_of_RH_hsw`: Chirre-Hagen's `ThetaRel`, `|θ(u) - u| ≤ u / 10^5` for `u ≥ 10^16`;
* `goldbach_12_hsw`: `goldbach_12` of Bilinear.lean with `ThetaRel` supplied by the above in
  place of a cited input, so it rests on Theorem 3 of Chirre-Hagen, the `4 · 10^18` check, RH
  and the three zero-count inputs.

Vacuity note: the three inputs hold for the true zeros if RH is true, by Hasanalizade-Shen-Wong
Corollary 1.2 for the counts and the first ordinate `14.1347...` for `Ordinates14`; the
hypotheses are about `gZ`, the actual zeta zeros, not a free family.

Binary Goldbach is OPEN.
-/

namespace LeanLab.PNTPort.ExplicitPsi1.ThetaRelRH

open Real Chebyshev
open LeanLab.Dudek2014.Section22
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14 S1 S2)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ psi_upper_gen psi_lower_gen)

/-- The lab's `psiF` is Mathlib's Chebyshev `ψ`. -/
lemma psiF_eq_psi (y : ℝ) : psiF y = ψ y := by
  unfold psiF
  rw [Chebyshev.psi_eq_sum_Icc]
  congr 1

lemma log_1e5_le : Real.log (10 ^ 5) ≤ 12 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : (2.7 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 :=
    pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) Real.exp_one_gt_d9.le) 12
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

lemma log_2pi_nonneg : 0 ≤ Real.log (2 * π) :=
  Real.log_nonneg (by linarith [Real.pi_gt_three])

lemma log_2pi_le : Real.log (2 * π) ≤ Real.log (10 ^ 5) :=
  Real.log_le_log (by positivity) (by linarith [Real.pi_le_four])

lemma S1_le : S1 (10 ^ 5) ≤ 26 := by
  unfold S1
  have a := log_1e5_le
  have b := log_2pi_nonneg
  have c := log_2pi_le
  have hpi := Real.pi_gt_three
  generalize Real.log (10 ^ 5) = L at *
  generalize Real.log (2 * π) = M at *
  have h1 : (L - M) ^ 2 ≤ 144 := by nlinarith
  have h2 : (L - M) ^ 2 / (2 * π) ≤ 24 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

lemma S2_le : S2 (10 ^ 5) ≤ 4 / 10 ^ 5 := by
  unfold S2
  have a := log_1e5_le
  have hpi := Real.pi_gt_three
  have l0 : 0 ≤ Real.log ((10 : ℝ) ^ 5) := Real.log_nonneg (by norm_num)
  generalize Real.log (10 ^ 5) = L at *
  have t1 : L / (π * 10 ^ 5) ≤ 4 / 10 ^ 5 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have t2 : (1.004 * L + 41.26 - 0.25 * 10 ^ 5) / ((10 : ℝ) ^ 5) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num; linarith) (by positivity)
  generalize L / (π * 10 ^ 5) = A at *
  generalize (1.004 * L + 41.26 - 0.25 * 10 ^ 5) / ((10 : ℝ) ^ 5) ^ 2 = B at *
  linarith

/-- For `y ≥ 10^16`, `w = y^{1/2}` has `w ≥ 10^8` and `w ≤ y / 10^8`. -/
lemma half_facts {y : ℝ} (hy : 10 ^ 16 ≤ y) :
    (y ^ (1 / 2 : ℝ)) ^ 2 = y ∧ y ^ (3 / 2 : ℝ) = y * y ^ (1 / 2 : ℝ) ∧
      0 ≤ y ^ (1 / 2 : ℝ) ∧ y ^ (1 / 2 : ℝ) ≤ y / 10 ^ 8 := by
  have hy0 : 0 < y := by linarith
  have hw2 : (y ^ (1 / 2 : ℝ)) ^ 2 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  have hw32 : y ^ (3 / 2 : ℝ) = y * y ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_one]
  have hw0 : 0 ≤ y ^ (1 / 2 : ℝ) := Real.rpow_nonneg hy0.le _
  refine ⟨hw2, hw32, hw0, ?_⟩
  set w := y ^ (1 / 2 : ℝ)
  have hw8 : 10 ^ 8 ≤ w := by nlinarith
  rw [le_div_iff₀ (by norm_num)]; nlinarith

/-- **Upper bound** `ψ(x) - x ≤ 2 x / 10^6` for `x ≥ 10^16`, under RH, CONDITIONAL ON `HSWN70`,
`HSWHead14`, `Ordinates14`. -/
theorem psi_sub_le_rh (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (hx : 10 ^ 16 ≤ x) : psiF x - x ≤ 2 * x / 10 ^ 6 := by
  have hx0 : 0 < x := by linarith
  have U := psi_upper_gen hRH hN hH h14 (x := x) (h := x / 10 ^ 6) (T := 10 ^ 5) (by linarith)
    (by positivity) (by norm_num)
  obtain ⟨-, hw32, hw0, hwle⟩ := half_facts (by linarith : (10 : ℝ) ^ 16 ≤ x + x / 10 ^ 6)
  rw [hw32] at U
  set w := (x + x / 10 ^ 6) ^ (1 / 2 : ℝ)
  have hS1 : w * S1 (10 ^ 5) ≤ w * 26 := mul_le_mul_of_nonneg_left S1_le hw0
  have hD : 2 * ((x + x / 10 ^ 6) * w) * S2 (10 ^ 5) / (x / 10 ^ 6) ≤
      2 * ((x + x / 10 ^ 6) * w) * (4 / 10 ^ 5) / (x / 10 ^ 6) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left S2_le (by positivity)) (by positivity)
  have eD : 2 * ((x + x / 10 ^ 6) * w) * (4 / 10 ^ 5) / (x / 10 ^ 6) = 80 * (1 + 1 / 10 ^ 6) * w := by
    field_simp; ring
  have hB : 4.786 / (x / 10 ^ 6) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hL := log_2pi_nonneg
  have hw' : w ≤ x * (1 + 1 / 10 ^ 6) / 10 ^ 8 := by
    have : x + x / 10 ^ 6 = x * (1 + 1 / 10 ^ 6) := by ring
    rw [← this]; exact hwle
  rw [eD] at hD
  generalize 2 * ((x + x / 10 ^ 6) * w) * S2 (10 ^ 5) / (x / 10 ^ 6) = D at *
  generalize 4.786 / (x / 10 ^ 6) = B at *
  generalize w * S1 (10 ^ 5) = C at *
  generalize Real.log (2 * π) = M at *
  linarith

/-- **Lower bound** `x - ψ(x) ≤ 2 x / 10^6` for `x ≥ 10^16`, under RH, CONDITIONAL ON `HSWN70`,
`HSWHead14`, `Ordinates14`. -/
theorem sub_psi_le_rh (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (hx : 10 ^ 16 ≤ x) : x - psiF x ≤ 2 * x / 10 ^ 6 := by
  have hx0 : 0 < x := by linarith
  have U := psi_lower_gen hRH hN hH h14 (x := x) (h := x / 10 ^ 6) (T := 10 ^ 5) (by linarith)
    (by positivity) (by norm_num)
  obtain ⟨-, hw32, hw0, hwle⟩ := half_facts hx
  rw [hw32] at U
  set w := x ^ (1 / 2 : ℝ)
  have hS1 : w * S1 (10 ^ 5) ≤ w * 26 := mul_le_mul_of_nonneg_left S1_le hw0
  have hD : 2 * (x * w) * S2 (10 ^ 5) / (x / 10 ^ 6) ≤ 2 * (x * w) * (4 / 10 ^ 5) / (x / 10 ^ 6) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left S2_le (by positivity)) (by positivity)
  have eD : 2 * (x * w) * (4 / 10 ^ 5) / (x / 10 ^ 6) = 80 * w := by
    field_simp; ring
  have hB : 4.786 / (x / 10 ^ 6) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hL : Real.log (2 * π) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * π)
    linarith [Real.pi_le_four]
  rw [eD] at hD
  generalize 2 * (x * w) * S2 (10 ^ 5) / (x / 10 ^ 6) = D at *
  generalize 4.786 / (x / 10 ^ 6) = B at *
  generalize w * S1 (10 ^ 5) = C at *
  generalize Real.log (2 * π) = M at *
  linarith

/-- `ψ(x) - θ(x) ≤ 76 x / 10^8` for `x ≥ 10^16`, from Mathlib's `ψ - θ ≤ 2 √x log x`. -/
theorem psi_sub_theta_le_small {x : ℝ} (hx : 10 ^ 16 ≤ x) : ψ x - θ x ≤ 76 * x / 10 ^ 8 := by
  have hx0 : 0 < x := by linarith
  refine le_trans (Chebyshev.psi_sub_theta_le (by linarith)) ?_
  set s := √x with hs
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs8 : 10 ^ 8 ≤ s := by nlinarith
  have hlog : Real.log x = 2 * Real.log s := by
    rw [hs, Real.log_sqrt hx0.le]; ring
  have h8 : Real.log (10 ^ 8) ≤ 19 := LeanLab.ChirreHagen2025.log_1e8_le
  have hq : Real.log (s / 10 ^ 8) ≤ s / 10 ^ 8 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at hq
  generalize Real.log (10 ^ 8) = M at *
  have hls : Real.log s ≤ 18 + s / 10 ^ 8 := by linarith
  have hm : s * Real.log s ≤ s * (18 + s / 10 ^ 8) := mul_le_mul_of_nonneg_left hls hs0
  rw [hlog]
  nlinarith

/-- `|θ(u) - u| ≤ 3 u / 10^6` for `u ≥ 10^16`, under RH, CONDITIONAL ON `HSWN70`, `HSWHead14`,
`Ordinates14`. -/
theorem abs_theta_sub_le_rh (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {u : ℝ} (hu : 10 ^ 16 ≤ u) : |θ u - u| ≤ 3 * u / 10 ^ 6 := by
  have a := psi_sub_le_rh hRH hN hH h14 hu
  have b := sub_psi_le_rh hRH hN hH h14 hu
  rw [psiF_eq_psi] at a b
  have c := psi_sub_theta_le_small hu
  have d := Chebyshev.theta_le_psi u
  rw [abs_le]; constructor <;> linarith

/-- **Chirre-Hagen's `ThetaRel`**, under RH, CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`
for the true ordinates; no Schoenfeld citation. -/
theorem thetaRel_of_RH_hsw (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    LeanLab.ChirreHagen2025.ThetaRel := by
  intro u hu
  have := abs_theta_sub_le_rh hRH hN hH h14 hu
  have hu0 : 0 < u := by linarith
  linarith

/-- `goldbach_12` with `ThetaRel` from `thetaRel_of_RH_hsw`: under RH, CONDITIONAL ON Chirre-Hagen
Theorem 3 `h3`, the `4 · 10^18` even check and the three zero-count inputs, a Goldbach number lies
in `(x, x + 12 log² x)` for every `x ≥ 2`. -/
theorem goldbach_12_hsw
    (h3 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      LeanLab.ChirreHagen2025.Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, LeanLab.ChirreHagen2025.IsGoldbachNumber n ∧ x < n ∧
        (n : ℝ) < x + 12 * Real.log x ^ 2 :=
  LeanLab.ChirreHagen2025.goldbach_12 h3 hE (thetaRel_of_RH_hsw hRH hN hH h14) hRH

end LeanLab.PNTPort.ExplicitPsi1.ThetaRelRH
