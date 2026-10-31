/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T1803Z-10253, unit U-0966.
P0021 Bordignon, Starichkova 2022, arXiv 2211.08844 v1, Lemma 11.

Lemma 11 writes V(x) = (U_N / log x) · P with
  P = (1 + θ₁(3 log x + 5)/(8π√x)) (1 + 2θ₂/x) (1 + 8θ₃ log N / x) (1 + θ₄/(x − 1)),
|θᵢ| ≤ 1, citing Nathanson Theorem 10.3 and Schoenfeld 1976 for that display, and then
claims "in particular" |P − 1| < 0.62 log N / N^{1/16} at x = N^{1/8} and
|P − 1| < 0.06 log N / N^{1/6} at x = N^{1/3}, for N ≥ 4·10¹⁸.

PROVED here, no cited input, for every N ≥ 4·10¹⁸ and every θᵢ ∈ [−1, 1]:
* `lemma11_z`: |P − 1| < 0.62 log N / N^{1/16} at x = N^{1/8}; the proved factor, from s ≥ 14.539 and t ≤ 42.83/14.539, is about 0.6149.
* `lemma11_y`: |P − 1| < 0.06 log N / N^{1/6} at x = N^{1/3}; proved with the cruder s ≥ 1096, still below 0.06; the true worst ratio is 0.0508.
Both MATCH. The display for V(x) itself stays cited.
Goldbach is open.
-/
import Mathlib
import LeanLab.BS2022GRH.Constants

open Real

noncomputable section
namespace LeanLab.BS2022GRH

lemma prod2 {u v e f : ℝ} (hu : |u| ≤ e) (hv : |v| ≤ f) :
    |(1 + u) * (1 + v) - 1| ≤ (1 + e) * (1 + f) - 1 := by
  have e0 : 0 ≤ e := le_trans (abs_nonneg _) hu
  have : (1 + u) * (1 + v) - 1 = u + v + u * v := by ring
  rw [this]
  calc |u + v + u * v| ≤ |u| + |v| + |u| * |v| := by
        rw [← abs_mul]; exact le_trans (abs_add_le _ _) (by gcongr; exact abs_add_le _ _)
    _ ≤ e + f + e * f := by gcongr
    _ = (1 + e) * (1 + f) - 1 := by ring

lemma theta_le {θ e : ℝ} (hθ : |θ| ≤ 1) (he : 0 ≤ e) : |θ * e| ≤ e := by
  rw [abs_mul, abs_of_nonneg he]; nlinarith [abs_nonneg θ]

/-- The four-factor bound: |∏(1 + θᵢeᵢ) − 1| ≤ t · H with H a polynomial in T and the Bᵢ,
whenever 0 ≤ eᵢ ≤ t Bᵢ and 0 ≤ t ≤ T. -/
lemma prod4 {θ₁ θ₂ θ₃ θ₄ e₁ e₂ e₃ e₄ t T B₁ B₂ B₃ B₄ : ℝ}
    (h1 : |θ₁| ≤ 1) (h2 : |θ₂| ≤ 1) (h3 : |θ₃| ≤ 1) (h4 : |θ₄| ≤ 1)
    (p1 : 0 ≤ e₁) (p2 : 0 ≤ e₂) (p3 : 0 ≤ e₃) (p4 : 0 ≤ e₄)
    (q1 : e₁ ≤ t * B₁) (q2 : e₂ ≤ t * B₂) (q3 : e₃ ≤ t * B₃) (q4 : e₄ ≤ t * B₄)
    (ht : 0 ≤ t) (hT : t ≤ T) (b1 : 0 ≤ B₁) (b2 : 0 ≤ B₂) (b3 : 0 ≤ B₃) (b4 : 0 ≤ B₄) :
    |(1 + θ₁ * e₁) * (1 + θ₂ * e₂) * (1 + θ₃ * e₃) * (1 + θ₄ * e₄) - 1| ≤
      t * (B₁ + B₂ + B₃ + B₄ + T * (B₁ * B₂ + B₁ * B₃ + B₁ * B₄ + B₂ * B₃ + B₂ * B₄ + B₃ * B₄)
        + T ^ 2 * (B₁ * B₂ * B₃ + B₁ * B₂ * B₄ + B₁ * B₃ * B₄ + B₂ * B₃ * B₄)
        + T ^ 3 * (B₁ * B₂ * B₃ * B₄)) := by
  have s12 := prod2 (theta_le h1 p1) (theta_le h2 p2)
  have s34 := prod2 (theta_le h3 p3) (theta_le h4 p4)
  have w12 : |(1 + θ₁ * e₁) * (1 + θ₂ * e₂) - 1| ≤ (1 + e₁) * (1 + e₂) - 1 := s12
  have key := prod2 w12 s34
  have e : (1 + θ₁ * e₁) * (1 + θ₂ * e₂) * (1 + θ₃ * e₃) * (1 + θ₄ * e₄) - 1 =
      (1 + ((1 + θ₁ * e₁) * (1 + θ₂ * e₂) - 1)) * (1 + ((1 + θ₃ * e₃) * (1 + θ₄ * e₄) - 1)) - 1 := by
    ring
  rw [e]
  refine le_trans key ?_
  have f : (1 + ((1 + e₁) * (1 + e₂) - 1)) * (1 + ((1 + e₃) * (1 + e₄) - 1)) - 1 =
      (1 + e₁) * (1 + e₂) * (1 + e₃) * (1 + e₄) - 1 := by ring
  rw [f]
  have g : (1 + e₁) * (1 + e₂) * (1 + e₃) * (1 + e₄) ≤
      (1 + t * B₁) * (1 + t * B₂) * (1 + t * B₃) * (1 + t * B₄) := by gcongr
  have hpoly : (1 + t * B₁) * (1 + t * B₂) * (1 + t * B₃) * (1 + t * B₄) - 1 =
      t * (B₁ + B₂ + B₃ + B₄ + t * (B₁ * B₂ + B₁ * B₃ + B₁ * B₄ + B₂ * B₃ + B₂ * B₄ + B₃ * B₄)
        + t ^ 2 * (B₁ * B₂ * B₃ + B₁ * B₂ * B₄ + B₁ * B₃ * B₄ + B₂ * B₃ * B₄)
        + t ^ 3 * (B₁ * B₂ * B₃ * B₄)) := by ring
  have hmono : B₁ + B₂ + B₃ + B₄ + t * (B₁ * B₂ + B₁ * B₃ + B₁ * B₄ + B₂ * B₃ + B₂ * B₄ + B₃ * B₄)
        + t ^ 2 * (B₁ * B₂ * B₃ + B₁ * B₂ * B₄ + B₁ * B₃ * B₄ + B₂ * B₃ * B₄)
        + t ^ 3 * (B₁ * B₂ * B₃ * B₄) ≤
      B₁ + B₂ + B₃ + B₄ + T * (B₁ * B₂ + B₁ * B₃ + B₁ * B₄ + B₂ * B₃ + B₂ * B₄ + B₃ * B₄)
        + T ^ 2 * (B₁ * B₂ * B₃ + B₁ * B₂ * B₄ + B₁ * B₃ * B₄ + B₂ * B₃ * B₄)
        + T ^ 3 * (B₁ * B₂ * B₃ * B₄) := by gcongr
  nlinarith [mul_le_mul_of_nonneg_left hmono ht]

/-- e^{L/k} ≥ e^{L₀/k} · L / L₀ for L ≥ L₀ ≥ k > 0. -/
lemma expLk_ge {k L₀ L : ℝ} (hk : 0 < k) (hk0 : k ≤ L₀) (hL : L₀ ≤ L) :
    exp (L₀ / k) * (L / L₀) ≤ exp (L / k) := by
  have hL0 : 0 < L₀ := by linarith
  have e : L / k = L₀ / k + (L - L₀) / k := by ring
  rw [e, exp_add]
  have h1 := Real.add_one_le_exp ((L - L₀) / k)
  have h2 : L / L₀ ≤ (L - L₀) / k + 1 := by
    rw [div_le_iff₀ hL0, add_mul, div_mul_eq_mul_div, one_mul]
    have : (L - L₀) * L₀ / k ≥ (L - L₀) * 1 := by
      rw [ge_iff_le, le_div_iff₀ hk]; nlinarith
    linarith
  exact mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le

lemma exp_z_ge : (14.539 : ℝ) ≤ exp (42.83 / 16) := by
  have e : (42.83 / 16 : ℝ) = ((2 : ℕ) : ℝ) + 0.676875 := by norm_num
  rw [e, exp_add]
  have h2 : (1.96767 : ℝ) ≤ exp 0.676875 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.676875 : ℝ)) (by norm_num) 14
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  calc (14.539 : ℝ) ≤ 2.7182818283 ^ 2 * 1.96767 := by norm_num
    _ ≤ exp ((2 : ℕ) : ℝ) * exp 0.676875 := by gcongr; exact exp_nat_ge 2

lemma exp_y_ge : (1096 : ℝ) ≤ exp (42.83 / 6) := by
  have h := exp_nat_ge 7
  have : exp ((7 : ℕ) : ℝ) ≤ exp (42.83 / 6) := exp_le_exp.mpr (by norm_num)
  have : (1096 : ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
  linarith

/-- Common core: with L = log N ≥ 42.83 and s = e^{L/(2m)}, x = s², the bound on |P − 1|. -/
lemma core {L s c S₀ T₀ B₁ : ℝ} {θ₁ θ₂ θ₃ θ₄ : ℝ}
    (h1 : |θ₁| ≤ 1) (h2 : |θ₂| ≤ 1) (h3 : |θ₃| ≤ 1) (h4 : |θ₄| ≤ 1)
    (hL : 42.83 ≤ L) (hs : S₀ ≤ s) (hS0 : 2 ≤ S₀) (ht : L / s ≤ T₀) (hc : 0 ≤ c)
    (hB1 : (c * L + 5) / (8 * π) ≤ L * B₁) :
    |(1 + θ₁ * ((c * L + 5) / (8 * π * s))) * (1 + θ₂ * (2 / s ^ 2)) *
        (1 + θ₃ * (8 * L / s ^ 2)) * (1 + θ₄ * (1 / (s ^ 2 - 1))) - 1| ≤
      L / s * (B₁ + 2 / (42.83 * S₀) + 8 / S₀ + 1 / (42.83 * (S₀ - 1 / S₀))
        + T₀ * (B₁ * (2 / (42.83 * S₀)) + B₁ * (8 / S₀) + B₁ * (1 / (42.83 * (S₀ - 1 / S₀)))
          + 2 / (42.83 * S₀) * (8 / S₀) + 2 / (42.83 * S₀) * (1 / (42.83 * (S₀ - 1 / S₀)))
          + 8 / S₀ * (1 / (42.83 * (S₀ - 1 / S₀))))
        + T₀ ^ 2 * (B₁ * (2 / (42.83 * S₀)) * (8 / S₀) + B₁ * (2 / (42.83 * S₀)) * (1 / (42.83 * (S₀ - 1 / S₀)))
          + B₁ * (8 / S₀) * (1 / (42.83 * (S₀ - 1 / S₀)))
          + 2 / (42.83 * S₀) * (8 / S₀) * (1 / (42.83 * (S₀ - 1 / S₀))))
        + T₀ ^ 3 * (B₁ * (2 / (42.83 * S₀)) * (8 / S₀) * (1 / (42.83 * (S₀ - 1 / S₀))))) := by
  have hsp : 0 < s := by linarith
  have hLp : 0 < L := by linarith
  have hS0p : 0 < S₀ := by linarith
  have hpi := Real.pi_pos
  have hs2 : 0 < s ^ 2 - 1 := by nlinarith
  have hD0 : 0 < S₀ - 1 / S₀ := by
    rw [sub_pos, div_lt_iff₀ hS0p]; nlinarith
  have hB1p : 0 ≤ B₁ := by
    have : 0 < (c * L + 5) / (8 * π) := by positivity
    by_contra h; push Not at h; nlinarith
  apply prod4 h1 h2 h3 h4 (by positivity) (by positivity) (by positivity) (by positivity)
  · -- e₁ ≤ t B₁
    rw [div_mul_eq_mul_div, le_div_iff₀ hsp]
    calc (c * L + 5) / (8 * π * s) * s = (c * L + 5) / (8 * π) := by field_simp
      _ ≤ L * B₁ := hB1
  · rw [div_mul_eq_mul_div, le_div_iff₀ hsp, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : 2 * s * (42.83 * S₀) ≤ L * (2 / (42.83 * S₀)) * s ^ 2 * (42.83 * S₀) := by
      have e : L * (2 / (42.83 * S₀)) * s ^ 2 * (42.83 * S₀) = 2 * L * s ^ 2 := by
        field_simp
      rw [e]; nlinarith [mul_le_mul hL hs (by linarith) (by linarith)]
    exact le_of_mul_le_mul_right this (by positivity)
  · rw [div_mul_eq_mul_div, le_div_iff₀ hsp, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have e : L * (8 / S₀) * s ^ 2 = 8 * L * s ^ 2 / S₀ := by ring
    rw [e, le_div_iff₀ hS0p]
    have : 0 ≤ 8 * L * s := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs this]
  · rw [div_mul_eq_mul_div, le_div_iff₀ hsp, div_mul_eq_mul_div, div_le_iff₀ hs2]
    -- s ≤ L B₄ (s² − 1) with B₄ = 1/(42.83 (S₀ − 1/S₀)), since s − 1/s ≥ S₀ − 1/S₀
    have hm : S₀ - 1 / S₀ ≤ s - 1 / s := by
      have : 1 / s ≤ 1 / S₀ := one_div_le_one_div_of_le hS0p hs
      linarith
    have e : 1 * s = s := one_mul s
    rw [e]
    have e2 : L * (1 / (42.83 * (S₀ - 1 / S₀))) * (s ^ 2 - 1) =
        (L / 42.83) * ((s - 1 / s) / (S₀ - 1 / S₀)) * s := by
      field_simp
    rw [e2]
    have r1 : 1 ≤ L / 42.83 := by rw [le_div_iff₀ (by norm_num)]; linarith
    have r2 : 1 ≤ (s - 1 / s) / (S₀ - 1 / S₀) := by rw [le_div_iff₀ hD0]; linarith
    have : 1 ≤ (L / 42.83) * ((s - 1 / s) / (S₀ - 1 / S₀)) := by nlinarith
    nlinarith
  · positivity
  · exact ht
  · exact hB1p
  · positivity
  · positivity
  · have : 0 < 42.83 * (S₀ - 1 / S₀) := by positivity
    positivity

/-- **Lemma 11 at x = N^{1/8}**: |P − 1| < 0.62 log N / N^{1/16} for N ≥ 4·10¹⁸. -/
theorem lemma11_z (N : ℝ) (hN : 4e18 ≤ N) (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h1 : |θ₁| ≤ 1) (h2 : |θ₂| ≤ 1) (h3 : |θ₃| ≤ 1) (h4 : |θ₄| ≤ 1) :
    let x := N ^ ((1 : ℝ) / 8)
    |(1 + θ₁ * ((3 * log x + 5) / (8 * π * sqrt x))) * (1 + θ₂ * (2 / x)) *
        (1 + θ₃ * (8 * log N / x)) * (1 + θ₄ * (1 / (x - 1))) - 1| <
      0.62 * (log N / N ^ ((1 : ℝ) / 16)) := by
  intro x
  have hN0 : 0 < N := by linarith
  have hL : 42.83 ≤ log N := le_trans logX_bounds.1 (Real.log_le_log (by norm_num) hN)
  set L := log N with hLd
  set s := exp (L / 16) with hsd
  have hx : x = s ^ 2 := by
    show N ^ ((1 : ℝ) / 8) = _
    rw [Real.rpow_def_of_pos hN0, hsd, ← exp_nat_mul]; congr 1; rw [hLd]; push_cast; ring
  have hsq : sqrt x = s := by
    rw [hx, Real.sqrt_sq (exp_pos _).le]
  have hlx : log x = L / 8 := by
    show log (N ^ ((1 : ℝ) / 8)) = _
    rw [Real.log_rpow hN0]; ring
  have hN16 : N ^ ((1 : ℝ) / 16) = s := by
    rw [Real.rpow_def_of_pos hN0, hsd]; congr 1; rw [hLd]; ring
  rw [hsq, hlx, hN16, hx]
  have hS := exp_z_ge
  have hs : (14.539 : ℝ) ≤ s := le_trans hS (exp_le_exp.mpr (by linarith))
  have hsp : 0 < s := exp_pos _
  have ht : L / s ≤ 42.83 / 14.539 := by
    have h := expLk_ge (k := 16) (by norm_num) (by norm_num) hL
    have h' : 14.539 * (L / 42.83) ≤ s := le_trans (mul_le_mul_of_nonneg_right hS (by positivity)) h
    rw [mul_div_assoc', div_le_iff₀ (by norm_num)] at h'
    rw [div_le_div_iff₀ hsp (by norm_num)]; linarith
  have hpi := Real.pi_gt_d4
  have e1 : (3 * (L / 8) + 5) = (3 / 8) * L + 5 := by ring
  rw [e1]
  have hB1 : ((3 / 8) * L + 5) / (8 * π) ≤ L * ((3 / 8 + 5 / 42.83) / (8 * 3.1415)) := by
    rw [div_le_iff₀ (by positivity)]
    have : (5 : ℝ) ≤ 5 / 42.83 * L := by rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
    have hLp : 0 < L := by linarith
    have : L * ((3 / 8 + 5 / 42.83) / (8 * 3.1415)) * (8 * π) =
        (3 / 8 * L + 5 / 42.83 * L) * (π / 3.1415) := by field_simp
    rw [this]
    have : 1 ≤ π / 3.1415 := by rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  have hcore := core h1 h2 h3 h4 hL hs (by norm_num) ht (by norm_num) hB1
  refine lt_of_le_of_lt hcore ?_
  have hLs : 0 < L / s := div_pos (by linarith) hsp
  rw [mul_comm (0.62 : ℝ)]
  apply mul_lt_mul_of_pos_left _ hLs
  norm_num

/-- **Lemma 11 at x = N^{1/3}**: |P − 1| < 0.06 log N / N^{1/6} for N ≥ 4·10¹⁸. -/
theorem lemma11_y (N : ℝ) (hN : 4e18 ≤ N) (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h1 : |θ₁| ≤ 1) (h2 : |θ₂| ≤ 1) (h3 : |θ₃| ≤ 1) (h4 : |θ₄| ≤ 1) :
    let x := N ^ ((1 : ℝ) / 3)
    |(1 + θ₁ * ((3 * log x + 5) / (8 * π * sqrt x))) * (1 + θ₂ * (2 / x)) *
        (1 + θ₃ * (8 * log N / x)) * (1 + θ₄ * (1 / (x - 1))) - 1| <
      0.06 * (log N / N ^ ((1 : ℝ) / 6)) := by
  intro x
  have hN0 : 0 < N := by linarith
  have hL : 42.83 ≤ log N := le_trans logX_bounds.1 (Real.log_le_log (by norm_num) hN)
  set L := log N with hLd
  set s := exp (L / 6) with hsd
  have hx : x = s ^ 2 := by
    show N ^ ((1 : ℝ) / 3) = _
    rw [Real.rpow_def_of_pos hN0, hsd, ← exp_nat_mul]; congr 1; rw [hLd]; push_cast; ring
  have hsq : sqrt x = s := by
    rw [hx, Real.sqrt_sq (exp_pos _).le]
  have hlx : log x = L / 3 := by
    show log (N ^ ((1 : ℝ) / 3)) = _
    rw [Real.log_rpow hN0]; ring
  have hN6 : N ^ ((1 : ℝ) / 6) = s := by
    rw [Real.rpow_def_of_pos hN0, hsd]; congr 1; rw [hLd]; ring
  rw [hsq, hlx, hN6, hx]
  have hS := exp_y_ge
  have hs : (1096 : ℝ) ≤ s := le_trans hS (exp_le_exp.mpr (by linarith))
  have hsp : 0 < s := exp_pos _
  have ht : L / s ≤ 42.83 / 1096 := by
    have h := expLk_ge (k := 6) (by norm_num) (by norm_num) hL
    have h' : 1096 * (L / 42.83) ≤ s := le_trans (mul_le_mul_of_nonneg_right hS (by positivity)) h
    rw [mul_div_assoc', div_le_iff₀ (by norm_num)] at h'
    rw [div_le_div_iff₀ hsp (by norm_num)]; linarith
  have hpi := Real.pi_gt_d4
  have e1 : (3 * (L / 3) + 5) = 1 * L + 5 := by ring
  rw [e1]
  have hB1 : (1 * L + 5) / (8 * π) ≤ L * ((1 + 5 / 42.83) / (8 * 3.1415)) := by
    rw [div_le_iff₀ (by positivity)]
    have : (5 : ℝ) ≤ 5 / 42.83 * L := by rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
    have hLp : 0 < L := by linarith
    have : L * ((1 + 5 / 42.83) / (8 * 3.1415)) * (8 * π) =
        (1 * L + 5 / 42.83 * L) * (π / 3.1415) := by field_simp
    rw [this]
    have : 1 ≤ π / 3.1415 := by rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  have hcore := core h1 h2 h3 h4 hL hs (by norm_num) ht (by norm_num) hB1
  refine lt_of_le_of_lt hcore ?_
  have hLs : 0 < L / s := div_pos (by linarith) hsp
  rw [mul_comm (0.06 : ℝ)]
  apply mul_lt_mul_of_pos_left _ hLs
  norm_num

end LeanLab.BS2022GRH
