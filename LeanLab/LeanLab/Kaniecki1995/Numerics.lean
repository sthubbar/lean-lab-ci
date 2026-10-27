/-
Kaniecki 1995, P0022: the numerical constants of Lemmas 4, 5 and Section 3, pp. 364-373.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Kaniecki1995.ExpBounds
import LeanLab.Kaniecki1995.Statements

namespace LeanLab.Kaniecki1995
open Real Finset

/-! ### Basic constants -/

theorem acK_eq : aK * cK = 2.5999655005 := by norm_num [aK, cK]

theorem exp_neg_cK_le : Real.exp (-cK) ≤ 0.2667376 := by
  have : -cK = -(((1 : ℕ) : ℝ) + 0.32149) := by norm_num [cK]
  rw [this]
  exact exp_neg_le (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem exp_neg_acK_le : Real.exp (-(aK * cK)) ≤ 0.07427616 := by
  have : -(aK * cK) = -(((2 : ℕ) : ℝ) + 0.5999655005) := by norm_num [aK, cK]
  rw [this]
  exact exp_neg_le (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem exp51_ge : (1.4e22 : ℝ) ≤ Real.exp 51 := by
  have h := nat_le_exp 51
  push_cast at h
  exact le_trans (by norm_num) h

theorem exp51_le : Real.exp 51 ≤ 1.41e22 := by
  have h := exp_nat_le 51
  push_cast at h
  exact le_trans h (by norm_num)

/-- Facts on `T ≥ e^{L₀}`, `L₀ ≥ 51`. -/
theorem T_facts {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) :
    1.4e22 ≤ T ∧ 0 < T ∧ L0 ≤ Real.log T := by
  have h51 : Real.exp 51 ≤ Real.exp L0 := Real.exp_le_exp.2 hL0
  have h1 : (1.4e22 : ℝ) ≤ T := exp51_ge.trans (h51.trans hT)
  have h0 : 0 < T := lt_of_lt_of_le (by norm_num) h1
  refine ⟨h1, h0, ?_⟩
  calc L0 = Real.log (Real.exp L0) := (Real.log_exp L0).symm
    _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hT

theorem sig_facts {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) :
    0 < sig aK cK T ∧ sig aK cK T ≤ 0.551 ∧ 0.9999999999999999999999 ≤ 1 - sig aK cK T / T := by
  obtain ⟨h1, h0, hL⟩ := T_facts hL0 hT
  have hLpos : 0 < Real.log T := by linarith
  have hs : sig aK cK T = 1 / 2 + 2.5999655005 / Real.log T := by rw [sig, acK_eq]
  have hq : 2.5999655005 / Real.log T ≤ 2.5999655005 / 51 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hq0 : 0 < 2.5999655005 / Real.log T := by positivity
  have hsp : 0 < sig aK cK T := by rw [hs]; linarith
  have hsl : sig aK cK T ≤ 0.551 := by rw [hs]; linarith [show (2.5999655005 : ℝ) / 51 ≤ 0.051 by norm_num]
  refine ⟨hsp, hsl, ?_⟩
  have : sig aK cK T / T ≤ 1e-22 := by
    rw [div_le_iff₀ h0]
    nlinarith
  linarith

/-! ### `f₁`, ..., `f₇` -/

theorem f1_le {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) {T0 : ℝ} (hT0 : 1.4e22 ≤ T0)
    (hTT0 : T0 ≤ T) :
    f1 T ≤ 504 / (T0 * L0) * (1 / (1 - 7.02 / 1.4e22)) ^ 2 := by
  obtain ⟨h1, h0, hL⟩ := T_facts hL0 hT
  unfold f1
  have hT0p : 0 < T0 := lt_of_lt_of_le (by norm_num) hT0
  have hd : 7.02 / T ≤ 7.02 / 1.4e22 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1
  have hpos : (0 : ℝ) < 1 - 7.02 / 1.4e22 := by norm_num
  have hpos' : 0 < 1 - 7.02 / T := by linarith
  apply mul_le_mul
  · apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul hTT0 hL (by linarith) h0.le
  · apply pow_le_pow_left₀ (by positivity)
    exact one_div_le_one_div_of_le hpos (by linarith)
  · positivity
  · positivity

theorem f2_lt {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) : f2 aK cK T < 0.11619 := by
  obtain ⟨_, _, hs⟩ := sig_facts hL0 hT
  have hpos : 0 < 1 - sig aK cK T / T := lt_of_lt_of_le (by norm_num) hs
  unfold f2
  have hb : 1 / (4 * aK ^ 2 * cK ^ 2) - 0.144 / Real.log T ^ 2 ≤ 1 / (4 * aK ^ 2 * cK ^ 2) := by
    have : 0 ≤ 0.144 / Real.log T ^ 2 := by positivity
    linarith
  calc π / (1 - sig aK cK T / T) * (1 / (4 * aK ^ 2 * cK ^ 2) - 0.144 / Real.log T ^ 2)
      ≤ π / (1 - sig aK cK T / T) * (1 / (4 * aK ^ 2 * cK ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (div_nonneg Real.pi_pos.le hpos.le)
    _ ≤ 3.14159265358979323847 / 0.9999999999999999999999 * (1 / (4 * aK ^ 2 * cK ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div₀ (by norm_num) Real.pi_lt_d20.le (by norm_num)
        linarith
    _ < 0.11619 := by norm_num [aK, cK]

theorem E_le : Real.exp (-cK) + Real.exp (-(aK * cK)) ≤ 0.34101376 := by
  linarith [exp_neg_cK_le, exp_neg_acK_le]

theorem f5_lt : f5 aK cK < 1.85985 := by
  unfold f5
  have hE := E_le
  have hA : (aK - 1) * cK = 1.2784755005 := by norm_num [aK, cK]
  rw [hA]
  have hd : 1.2784755005 - 0.34101376 ≤ 1.2784755005 - Real.exp (-cK) - Real.exp (-(aK * cK)) := by
    linarith
  have hdp : (0 : ℝ) < 1.2784755005 - 0.34101376 := by norm_num
  calc (1.2784755005 / (1.2784755005 - Real.exp (-cK) - Real.exp (-(aK * cK)))) ^ 2
      ≤ (1.2784755005 / (1.2784755005 - 0.34101376)) ^ 2 := by
        apply pow_le_pow_left₀ (div_nonneg (by norm_num) (by linarith))
        exact div_le_div_of_nonneg_left (by norm_num) hdp hd
    _ < 1.85985 := by norm_num

theorem f5_nonneg : 0 ≤ f5 aK cK := by unfold f5; positivity

/-- Generic bound for `f₃` given a lower bound `P` for `T^{α-1}`. -/
theorem f3_le {T L0 α P : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) (hP : 0 < P)
    (hPQ : P ≤ T ^ (α - 1)) (hα : 0 ≤ α) :
    f3 aK cK T α ≤ (α ^ 2 * 3.14159265358979323847 / 0.9999999999999999999999 +
      (2 + 1e-22) ^ 2 * (α ^ 2 / P + 2 * α / (P * L0) + 2 / (P * L0 ^ 2))) *
      (0.34101376 / (2 * (aK - 1) * cK)) ^ 2 := by
  obtain ⟨h1, h0, hL⟩ := T_facts hL0 hT
  obtain ⟨_, _, hs⟩ := sig_facts hL0 hT
  have hpos : 0 < 1 - sig aK cK T / T := lt_of_lt_of_le (by norm_num) hs
  have hL0p : 0 < L0 := by linarith
  have hQ : 0 < T ^ (α - 1) := lt_of_lt_of_le hP hPQ
  have hinvT : 1 / T ≤ 1e-22 := by
    rw [div_le_iff₀ h0]; nlinarith
  have hE := E_le
  have hE0 : 0 ≤ Real.exp (-cK) + Real.exp (-(aK * cK)) := by positivity
  have hden : 0 < 2 * (aK - 1) * cK := by norm_num [aK, cK]
  have hLT : 0 < Real.log T := by linarith
  have hb0 : 0 ≤ α ^ 2 / P + 2 * α / (P * L0) + 2 / (P * L0 ^ 2) :=
    add_nonneg (add_nonneg (div_nonneg (sq_nonneg _) hP.le)
      (div_nonneg (by linarith) (mul_pos hP hL0p).le))
      (div_nonneg (by norm_num) (mul_nonneg hP.le (sq_nonneg _)))
  have hq0 : 0 ≤ α ^ 2 / T ^ (α - 1) + 2 * α / (T ^ (α - 1) * Real.log T) +
      2 / (T ^ (α - 1) * Real.log T ^ 2) :=
    add_nonneg (add_nonneg (div_nonneg (sq_nonneg _) hQ.le)
      (div_nonneg (by linarith) (mul_pos hQ hLT).le))
      (div_nonneg (by norm_num) (mul_nonneg hQ.le (sq_nonneg _)))
  have hbr : 0 ≤ α ^ 2 * 3.14159265358979323847 / 0.9999999999999999999999 +
      (2 + 1e-22) ^ 2 * (α ^ 2 / P + 2 * α / (P * L0) + 2 / (P * L0 ^ 2)) :=
    add_nonneg (by positivity) (mul_nonneg (by positivity) hb0)
  unfold f3
  apply mul_le_mul _ _ (by positivity) hbr
  · apply add_le_add
    · apply div_le_div₀ (by positivity) _ (by norm_num) (by linarith)
      exact mul_le_mul_of_nonneg_left Real.pi_lt_d20.le (by positivity)
    · apply mul_le_mul _ _ hq0 (by positivity)
      · apply pow_le_pow_left₀ (by positivity); linarith
      · apply add_le_add (add_le_add _ _) _
        · exact div_le_div_of_nonneg_left (by positivity) hP hPQ
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul hPQ hL hL0p.le hQ.le)
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul hPQ (pow_le_pow_left₀ hL0p.le hL 2) (by positivity) hQ.le)
  · apply pow_le_pow_left₀ (div_nonneg hE0 hden.le)
    exact div_le_div_of_nonneg_right hE hden.le

theorem rpow_ge_exp {T L0 k : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) (hk : 0 ≤ k) :
    Real.exp (L0 * k) ≤ T ^ k := by
  obtain ⟨_, h0, hL⟩ := T_facts hL0 hT
  rw [Real.rpow_def_of_pos h0]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hL hk)

theorem f3_set1 {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) : f3 aK cK T 1.07 < 0.06636 := by
  have hP : (35.5 : ℝ) ≤ T ^ ((1.07 : ℝ) - 1) := by
    have h357 : (35.5 : ℝ) ≤ Real.exp (((3 : ℕ) : ℝ) + 0.57) :=
      le_exp_add_nat (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have h2 := rpow_ge_exp (k := (1.07 : ℝ) - 1) hL0 hT (by norm_num)
    have h3 : Real.exp (((3 : ℕ) : ℝ) + 0.57) ≤ Real.exp (L0 * ((1.07 : ℝ) - 1)) :=
      Real.exp_le_exp.2 (by push_cast; nlinarith)
    linarith
  have hL51 : (51 : ℝ) ≤ L0 := hL0
  calc f3 aK cK T 1.07 ≤ _ := f3_le hL0 hT (by norm_num) hP (by norm_num)
    _ ≤ ((1.07 : ℝ) ^ 2 * 3.14159265358979323847 / 0.9999999999999999999999 +
      (2 + 1e-22) ^ 2 * ((1.07 : ℝ) ^ 2 / 35.5 + 2 * 1.07 / (35.5 * 51) + 2 / (35.5 * 51 ^ 2))) *
      (0.34101376 / (2 * (aK - 1) * cK)) ^ 2 := by
        gcongr
    _ < 0.06636 := by norm_num [aK, cK]

theorem f3_set2 {T : ℝ} (hT : Real.exp 83970 ≤ T) : f3 aK cK T 1.00013 < 0.055895 := by
  have hP : (55000 : ℝ) ≤ T ^ ((1.00013 : ℝ) - 1) := by
    have h357 : (55000 : ℝ) ≤ Real.exp (((10 : ℕ) : ℝ) + 0.9161) :=
      le_exp_add_nat (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have h2 := rpow_ge_exp (k := (1.00013 : ℝ) - 1) (by norm_num) hT (by norm_num)
    have h3 : Real.exp (((10 : ℕ) : ℝ) + 0.9161) ≤ Real.exp (83970 * ((1.00013 : ℝ) - 1)) :=
      Real.exp_le_exp.2 (by norm_num)
    linarith
  calc f3 aK cK T 1.00013 ≤ _ := f3_le (by norm_num) hT (by norm_num) hP (by norm_num)
    _ < 0.055895 := by norm_num [aK, cK]


theorem exp_neg12_le : Real.exp (-12) ≤ 1e-5 := by
  have : (-12 : ℝ) = -(((12 : ℕ) : ℝ) + 0) := by norm_num
  rw [this]
  exact exp_neg_le (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `0 ≤ β ≤ 0.0743` for `T ≥ e^{51}`; `β ~ e^{-ac} = 0.074276...`, p. 365. -/
theorem beta_bounds {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) :
    0 ≤ beta aK cK T ∧ beta aK cK T ≤ 0.0743 := by
  obtain ⟨h1, h0, hL⟩ := T_facts hL0 hT
  obtain ⟨hs0, _, _⟩ := sig_facts hL0 hT
  have ha : (0 : ℝ) < aK := by norm_num [aK]
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hS : (1e11 : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hS0 : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos h0 _
  unfold beta
  set x := T ^ (1 / aK) with hx
  have hx2 : (2 : ℝ) ≤ x := by
    have : T ^ (1 / 2 : ℝ) ≤ x := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num [aK])
    linarith
  have e1 : x ^ (aK / 2) = T ^ (1 / 2 : ℝ) := by
    rw [hx, ← Real.rpow_mul h0.le]; congr 1; field_simp
  have e2 : x ^ (1 / 2 : ℝ) = T ^ (1 / (2 * aK)) := by
    rw [hx, ← Real.rpow_mul h0.le]; congr 1; field_simp
  have e3 : x ^ (2 * aK) = T ^ 2 := by
    rw [hx, ← Real.rpow_mul h0.le, show 1 / aK * (2 * aK) = ((2 : ℕ) : ℝ) by field_simp; norm_num,
      Real.rpow_natCast]
  have hk : T ^ (1 / (2 * aK)) ≤ 1e-5 * T ^ (1 / 2 : ℝ) := by
    have : T ^ (1 / (2 * aK)) = T ^ (1 / 2 : ℝ) * T ^ (1 / (2 * aK) - 1 / 2) := by
      rw [← Real.rpow_add h0]; congr 1; ring
    rw [this, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hS0.le
    rw [Real.rpow_def_of_pos h0]
    have hc : 1 / (2 * aK) - 1 / 2 ≤ -0.24 := by norm_num [aK]
    calc Real.exp (Real.log T * (1 / (2 * aK) - 1 / 2)) ≤ Real.exp (-12) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ ≤ 1e-5 := exp_neg12_le
  have hxs : 1 ≤ x ^ sig aK cK T := Real.one_le_rpow (by linarith) hs0.le
  have hxas : 1 ≤ x ^ (aK * sig aK cK T) := Real.one_le_rpow (by linarith) (by positivity)
  have hx3 : 3 ≤ x ^ 2 - 1 := by nlinarith
  have hx4 : 3 ≤ x ^ (2 * aK) - 1 := by rw [e3]; nlinarith
  have t3p : 0 < 1 / (x ^ sig aK cK T * (x ^ 2 - 1)) := by
    apply div_pos one_pos; apply mul_pos <;> linarith
  have t3 : 1 / (x ^ sig aK cK T * (x ^ 2 - 1)) ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have t4p : 0 < 1 / (x ^ (aK * sig aK cK T) * (x ^ (2 * aK) - 1)) := by
    apply div_pos one_pos; apply mul_pos <;> linarith
  have t4 : 1 / (x ^ (aK * sig aK cK T) * (x ^ (2 * aK) - 1)) ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  rw [e1, e2]
  have hr0 : 0 ≤ T ^ (1 / (2 * aK)) := (Real.rpow_pos_of_pos h0 _).le
  constructor
  · apply div_nonneg _ hS0.le
    have := Real.exp_pos (-(aK * cK)); have := Real.exp_pos (-cK)
    positivity
  · rw [div_le_iff₀ hS0]
    have m1 : Real.exp (-(aK * cK)) * T ^ (1 / 2 : ℝ) ≤ 0.07427616 * T ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right exp_neg_acK_le hS0.le
    have m2 : Real.exp (-cK) * T ^ (1 / (2 * aK)) ≤ 0.2667376 * (1e-5 * T ^ (1 / 2 : ℝ)) :=
      mul_le_mul exp_neg_cK_le hk hr0 (by norm_num)
    nlinarith

theorem f4_le {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) :
    f4 aK cK T ≤ aK ^ 2 * 0.0743 ^ 2 * (1 + 1e-22) ^ 2 / (8232 * (aK - 1) ^ 2 * L0 ^ 4) := by
  obtain ⟨h1, h0, hL⟩ := T_facts hL0 hT
  obtain ⟨hs0, hs1, _⟩ := sig_facts hL0 hT
  obtain ⟨hb0, hb1⟩ := beta_bounds hL0 hT
  have hinvT : 1 / T ≤ 1e-22 := by rw [div_le_iff₀ h0]; nlinarith
  have hinv0 : 0 ≤ 1 / T := by positivity
  have hp : (1 + 1 / T) ^ (2 * sig aK cK T) ≤ (1 + 1e-22) ^ 2 := by
    calc (1 + 1 / T) ^ (2 * sig aK cK T) ≤ (1 + 1 / T) ^ ((2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
      _ = (1 + 1 / T) ^ 2 := Real.rpow_natCast _ 2
      _ ≤ (1 + 1e-22) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hp0 : 0 ≤ (1 + 1 / T) ^ (2 * sig aK cK T) := Real.rpow_nonneg (by positivity) _
  have hL0p : 0 < L0 := by linarith
  unfold f4
  apply div_le_div₀ (by positivity) _ (by norm_num [aK]; positivity) _
  · apply mul_le_mul _ hp hp0 (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb1 2) (by positivity)
  · apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0p.le hL 4) (by norm_num [aK])

theorem log_sq_div_le {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) :
    Real.log T ^ 2 / T ≤ 120 / L0 ^ 3 := by
  obtain ⟨h1, h0, hL⟩ := T_facts hL0 hT
  have hLp : 0 < Real.log T := by linarith
  have h5 : Real.log T ^ 5 / 120 ≤ T := by
    have := Real.pow_div_factorial_le_exp (Real.log T) hLp.le 5
    rw [Real.exp_log h0] at this
    simpa [Nat.factorial] using this
  calc Real.log T ^ 2 / T ≤ Real.log T ^ 2 / (Real.log T ^ 5 / 120) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h5
    _ = 120 / Real.log T ^ 3 := by field_simp
    _ ≤ 120 / L0 ^ 3 := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by linarith) hL 3)

theorem f6_le {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) :
    f6 aK cK T ≤ 3.14159265358979323847 / (0.9999999999999999999999 * L0 ^ 2) *
      (0.886 + 120 / L0 ^ 3 / (8 * aK ^ 2 * cK ^ 2) + 120 / L0 ^ 3 / 1.4e22) := by
  obtain ⟨h1, h0, hL⟩ := T_facts hL0 hT
  obtain ⟨hs0, hs1, hs⟩ := sig_facts hL0 hT
  have hLp : 0 < Real.log T := by linarith
  have hL0p : 0 < L0 := by linarith
  have hq := log_sq_div_le hL0 hT
  have hacp : (0 : ℝ) < aK * cK := by norm_num [aK, cK]
  have t2 : Real.log T ^ 2 / (8 * T * aK ^ 2 * cK ^ 2) ≤ 120 / L0 ^ 3 / (8 * aK ^ 2 * cK ^ 2) := by
    have : Real.log T ^ 2 / (8 * T * aK ^ 2 * cK ^ 2) = Real.log T ^ 2 / T / (8 * aK ^ 2 * cK ^ 2) := by
      field_simp
    rw [this]; exact div_le_div_of_nonneg_right hq (by positivity)
  have t3 : Real.log T / (4 * T ^ 2 * aK * cK) ≤ 120 / L0 ^ 3 / 1.4e22 := by
    have e : Real.log T / (4 * T ^ 2 * aK * cK) ≤ Real.log T ^ 2 / T / T := by
      have hd : 0 < 4 * T ^ 2 * aK * cK :=
        mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos h0 2)) (by norm_num [aK])) (by norm_num [cK])
      rw [div_div, div_le_div_iff₀ hd (by positivity)]
      have : 1 ≤ 4 * aK * cK * Real.log T := by nlinarith [show (1 : ℝ) ≤ 4 * aK * cK by norm_num [aK, cK]]
      have key : Real.log T * (T * T) ≤ Real.log T * (T * T) * (4 * aK * cK * Real.log T) :=
        le_mul_of_one_le_right (by positivity) this
      calc Real.log T * (T * T) ≤ Real.log T * (T * T) * (4 * aK * cK * Real.log T) := key
        _ = Real.log T ^ 2 * (4 * T ^ 2 * aK * cK) := by ring
    calc _ ≤ Real.log T ^ 2 / T / T := e
      _ ≤ 120 / L0 ^ 3 / 1.4e22 := div_le_div₀ (by positivity) hq (by norm_num) h1
  have hpos : 0 < 1 - sig aK cK T / T := lt_of_lt_of_le (by norm_num) hs
  have hn0 : 0 ≤ 0.886 + Real.log T ^ 2 / (8 * T * aK ^ 2 * cK ^ 2) +
      Real.log T / (4 * T ^ 2 * aK * cK) := by
    have d1 : 0 < 4 * T ^ 2 * aK * cK :=
      mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos h0 2)) (by norm_num [aK])) (by norm_num [cK])
    have d2 : 0 < 8 * T * aK ^ 2 * cK ^ 2 :=
      mul_pos (mul_pos (mul_pos (by norm_num) h0) (by norm_num [aK])) (by norm_num [cK])
    exact add_nonneg (add_nonneg (by norm_num) (div_nonneg (by positivity) d2.le))
      (div_nonneg hLp.le d1.le)
  unfold f6
  apply mul_le_mul _ _ hn0 (by positivity)
  · apply div_le_div₀ (by positivity) Real.pi_lt_d20.le (by positivity)
    exact mul_le_mul hs (pow_le_pow_left₀ hL0p.le hL 2) (by positivity) (by linarith)
  · linarith

theorem f7_le {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) :
    f7 aK cK T ≤ 4.51 * 3.14159265358979323847 / (0.9999999999999999999999 * L0 ^ 2) := by
  obtain ⟨h1, h0, hL⟩ := T_facts hL0 hT
  obtain ⟨hs0, hs1, hs⟩ := sig_facts hL0 hT
  have hL0p : 0 < L0 := by linarith
  unfold f7
  apply div_le_div₀ (by positivity) (by linarith [Real.pi_lt_d20]) (by positivity)
  exact mul_le_mul hs (pow_le_pow_left₀ hL0p.le hL 2) (by positivity) (by linarith)

/-! ### Set 1: `T ≥ e^{51}`, `a = 1.96745`, `c = 1.32149`, `α = 1.07`, p. 372 -/

theorem f1_set1 {T : ℝ} (hT : Real.exp 51 ≤ T) : f1 T < 1e-21 := by
  have := f1_le (le_refl 51) hT (le_refl _) (exp51_ge.trans hT)
  exact lt_of_le_of_lt this (by norm_num)

theorem f4_set1 {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) : f4 aK cK T < 5e-13 := by
  have h := f4_le hL0 hT
  have : aK ^ 2 * 0.0743 ^ 2 * (1 + 1e-22) ^ 2 / (8232 * (aK - 1) ^ 2 * L0 ^ 4) ≤
      aK ^ 2 * 0.0743 ^ 2 * (1 + 1e-22) ^ 2 / (8232 * (aK - 1) ^ 2 * 51 ^ 4) := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num [aK])
    apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hL0 4) (by norm_num [aK])
  have : aK ^ 2 * 0.0743 ^ 2 * (1 + 1e-22) ^ 2 / (8232 * (aK - 1) ^ 2 * 51 ^ 4) < 5e-13 := by
    norm_num [aK]
  linarith

theorem f6_set1 {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) : f6 aK cK T < 0.0010702 := by
  have h := f6_le hL0 hT
  have hL0p : 0 < L0 := by linarith
  have : 3.14159265358979323847 / (0.9999999999999999999999 * L0 ^ 2) *
      (0.886 + 120 / L0 ^ 3 / (8 * aK ^ 2 * cK ^ 2) + 120 / L0 ^ 3 / 1.4e22) ≤
      3.14159265358979323847 / (0.9999999999999999999999 * 51 ^ 2) *
      (0.886 + 120 / 51 ^ 3 / (8 * aK ^ 2 * cK ^ 2) + 120 / 51 ^ 3 / 1.4e22) := by
    have h3 : (120 : ℝ) / L0 ^ 3 ≤ 120 / 51 ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL0 3)
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · exact div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hL0 2) (by norm_num))
    · gcongr
  have : 3.14159265358979323847 / (0.9999999999999999999999 * 51 ^ 2) *
      (0.886 + 120 / 51 ^ 3 / (8 * aK ^ 2 * cK ^ 2) + 120 / 51 ^ 3 / 1.4e22) < (0.0010702 : ℝ) := by
    norm_num [aK, cK]
  linarith

theorem f7_set1 {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) : f7 aK cK T < 0.00544736 := by
  have h := f7_le hL0 hT
  have : 4.51 * 3.14159265358979323847 / (0.9999999999999999999999 * L0 ^ 2) ≤
      4.51 * 3.14159265358979323847 / (0.9999999999999999999999 * 51 ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hL0 2) (by norm_num))
  have : 4.51 * 3.14159265358979323847 / (0.9999999999999999999999 * 51 ^ 2) < (0.00544736 : ℝ) := by
    norm_num
  linarith

theorem sqrt_le_of {x b s : ℝ} (hx : x ≤ b) (hs : 0 ≤ s) (hb : b ≤ s ^ 2) : √x ≤ s :=
  (Real.sqrt_le_sqrt hx).trans ((Real.sqrt_le_left hs).2 hb)

/-- `f(a, c, T, α) < 0.66614` for `T ≥ e^{51}`, as printed p. 372; uses `f₁ < 10^{-21}`. -/
theorem fK_set1 {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) : fK aK cK T 1.07 < 0.66614 := by
  have h51 : Real.exp 51 ≤ T := (Real.exp_le_exp.2 hL0).trans hT
  have s2 := sqrt_le_of (f2_lt hL0 hT).le (by norm_num) (by norm_num : (0.11619 : ℝ) ≤ 0.340866543 ^ 2)
  have s3 := sqrt_le_of (f3_set1 hL0 hT).le (by norm_num) (by norm_num : (0.06636 : ℝ) ≤ 0.257604348 ^ 2)
  have s4 := sqrt_le_of (f4_set1 hL0 hT).le (by norm_num) (by norm_num : (5e-13 : ℝ) ≤ 7.08e-7 ^ 2)
  have hsum : (√(f2 aK cK T) + √(f3 aK cK T 1.07) + √(f4 aK cK T)) ^ 2 ≤
      (0.340866543 + 0.257604348 + 7.08e-7) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h5 := f5_lt
  have h50 := f5_nonneg
  have h1 := f1_set1 h51
  unfold fK
  have : (√(f2 aK cK T) + √(f3 aK cK T 1.07) + √(f4 aK cK T)) ^ 2 * f5 aK cK ≤
      (0.340866543 + 0.257604348 + 7.08e-7) ^ 2 * 1.85985 :=
    mul_le_mul hsum h5.le h50 (by positivity)
  have : (1e-21 : ℝ) + (0.340866543 + 0.257604348 + 7.08e-7) ^ 2 * 1.85985 < 0.66614 := by norm_num
  linarith

/-- `(1/π)(f^{1/2} + f₆^{1/2} + f₇^{1/2})² < 0.271`, giving (24), p. 372. -/
theorem Jconst_set1 {T L0 : ℝ} (hL0 : 51 ≤ L0) (hT : Real.exp L0 ≤ T) :
    1 / π * (√(fK aK cK T 1.07) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2 < 0.271 := by
  have s1 := sqrt_le_of (fK_set1 hL0 hT).le (by norm_num) (by norm_num : (0.66614 : ℝ) ≤ 0.816174002 ^ 2)
  have s6 := sqrt_le_of (f6_set1 hL0 hT).le (by norm_num) (by norm_num : (0.0010702 : ℝ) ≤ 0.032713912 ^ 2)
  have s7 := sqrt_le_of (f7_set1 hL0 hT).le (by norm_num) (by norm_num : (0.00544736 : ℝ) ≤ 0.073806233 ^ 2)
  have hsum : (√(fK aK cK T 1.07) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2 ≤
      (0.816174002 + 0.032713912 + 0.073806233) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hpi : 1 / π ≤ 1 / 3.14159265358979323846 :=
    one_div_le_one_div_of_le (by norm_num) Real.pi_gt_d20.le
  calc 1 / π * (√(fK aK cK T 1.07) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2
      ≤ 1 / 3.14159265358979323846 * (0.816174002 + 0.032713912 + 0.073806233) ^ 2 :=
        mul_le_mul hpi hsum (by positivity) (by norm_num)
    _ < 0.271 := by norm_num


/-! ### Set 2: `T ≥ e^{83970}`, `α = 1.00013`, p. 372 -/

theorem exp83970_ge : (10 : ℝ) ^ 36467 ≤ Real.exp 83970 := by
  have h10 : (10 : ℝ) ≤ Real.exp (((2 : ℕ) : ℝ) + 0.3026) :=
    le_exp_add_nat (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  calc (10 : ℝ) ^ 36467 ≤ Real.exp (((2 : ℕ) : ℝ) + 0.3026) ^ 36467 :=
        pow_le_pow_left₀ (by norm_num) h10 _
    _ = Real.exp ((36467 : ℕ) * (((2 : ℕ) : ℝ) + 0.3026)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp 83970 := Real.exp_le_exp.2 (by norm_num)

theorem exp83970_le : Real.exp 83970 ≤ (10 : ℝ) ^ 36468 := by
  have h10 : Real.exp (((2 : ℕ) : ℝ) + 0.30258) ≤ 10 :=
    exp_add_nat_le (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  calc Real.exp 83970 ≤ Real.exp ((36468 : ℕ) * (((2 : ℕ) : ℝ) + 0.30258)) :=
        Real.exp_le_exp.2 (by norm_num)
    _ = Real.exp (((2 : ℕ) : ℝ) + 0.30258) ^ 36468 := Real.exp_nat_mul _ _
    _ ≤ (10 : ℝ) ^ 36468 := pow_le_pow_left₀ (Real.exp_pos _).le h10 _

theorem ten_pow_ge {m n : ℕ} (h : m ≤ n) : (10 : ℝ) ^ m ≤ 10 ^ n :=
  pow_le_pow_right₀ (by norm_num) h

theorem f1_set2 {T : ℝ} (hT : Real.exp 83970 ≤ T) : f1 T < (10 : ℝ) ^ (-36469 : ℤ) := by
  have h22 : (1.4e22 : ℝ) ≤ 10 ^ 36467 :=
    le_trans (by norm_num : (1.4e22 : ℝ) ≤ 10 ^ 23) (ten_pow_ge (by norm_num))
  have := f1_le (by norm_num) hT h22 (exp83970_ge.trans hT)
  refine lt_of_le_of_lt this ?_
  set X : ℝ := 10 ^ 36467 with hX
  have hX0 : 0 < X := by positivity
  have e : (10 : ℝ) ^ (-36469 : ℤ) = (1 / 100) / X := by
    rw [zpow_neg, zpow_ofNat, hX, show 36469 = 36467 + 2 by norm_num, pow_add]
    field_simp; norm_num
  rw [e, show 504 / (X * 83970) * (1 / (1 - 7.02 / 1.4e22)) ^ 2 =
    (504 / 83970 * (1 / (1 - 7.02 / 1.4e22)) ^ 2) / X by field_simp]
  exact div_lt_div_of_pos_right (by norm_num) hX0

theorem f4_set2 {T : ℝ} (hT : Real.exp 83970 ≤ T) : f4 aK cK T < 1e-25 := by
  have h := f4_le (by norm_num) hT
  have : aK ^ 2 * 0.0743 ^ 2 * (1 + 1e-22) ^ 2 / (8232 * (aK - 1) ^ 2 * 83970 ^ 4) < (1e-25 : ℝ) := by
    norm_num [aK]
  linarith

theorem f6_set2 {T : ℝ} (hT : Real.exp 83970 ≤ T) : f6 aK cK T < 4e-10 := by
  have h := f6_le (by norm_num) hT
  have : 3.14159265358979323847 / (0.9999999999999999999999 * 83970 ^ 2) *
      (0.886 + 120 / 83970 ^ 3 / (8 * aK ^ 2 * cK ^ 2) + 120 / 83970 ^ 3 / 1.4e22) < (4e-10 : ℝ) := by
    norm_num [aK, cK]
  linarith

theorem f7_set2 {T : ℝ} (hT : Real.exp 83970 ≤ T) : f7 aK cK T < 2.01e-9 := by
  have h := f7_le (by norm_num) hT
  have : 4.51 * 3.14159265358979323847 / (0.9999999999999999999999 * 83970 ^ 2) < (2.01e-9 : ℝ) := by
    norm_num
  linarith

/-- `f(a, c, T, α) < 0.619816` for `T ≥ e^{83970}`, as printed p. 372; uses `f₁ < 10^{-36469}`. -/
theorem fK_set2 {T : ℝ} (hT : Real.exp 83970 ≤ T) : fK aK cK T 1.00013 < 0.619816 := by
  have s2 := sqrt_le_of (f2_lt (by norm_num) hT).le (by norm_num) (by norm_num : (0.11619 : ℝ) ≤ 0.340866543 ^ 2)
  have s3 := sqrt_le_of (f3_set2 hT).le (by norm_num) (by norm_num : (0.055895 : ℝ) ≤ 0.236421235 ^ 2)
  have s4 := sqrt_le_of (f4_set2 hT).le (by norm_num) (by norm_num : (1e-25 : ℝ) ≤ 1e-9 ^ 2)
  have hsum : (√(f2 aK cK T) + √(f3 aK cK T 1.00013) + √(f4 aK cK T)) ^ 2 ≤
      (0.340866543 + 0.236421235 + 1e-9) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h1 := f1_set2 hT
  unfold fK
  have : (√(f2 aK cK T) + √(f3 aK cK T 1.00013) + √(f4 aK cK T)) ^ 2 * f5 aK cK ≤
      (0.340866543 + 0.236421235 + 1e-9) ^ 2 * 1.85985 :=
    mul_le_mul hsum f5_lt.le f5_nonneg (by positivity)
  have hsmall : (10 : ℝ) ^ (-36469 : ℤ) ≤ 1e-30 := by
    rw [zpow_neg, zpow_ofNat]
    calc ((10 : ℝ) ^ 36469)⁻¹ ≤ ((10 : ℝ) ^ 30)⁻¹ :=
          inv_anti₀ (by positivity) (ten_pow_ge (by norm_num))
      _ = 1e-30 := by norm_num
  have : (1e-30 : ℝ) + (0.340866543 + 0.236421235 + 1e-9) ^ 2 * 1.85985 < 0.619816 := by
    norm_num
  linarith

/-- `(1/π)(f^{1/2} + f₆^{1/2} + f₇^{1/2})² < 0.1973261`, p. 373. -/
theorem Jconst_set2 {T : ℝ} (hT : Real.exp 83970 ≤ T) :
    1 / π * (√(fK aK cK T 1.00013) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2 < 0.1973261 := by
  have s1 := sqrt_le_of (fK_set2 hT).le (by norm_num) (by norm_num : (0.619816 : ℝ) ≤ 0.787283939 ^ 2)
  have s6 := sqrt_le_of (f6_set2 hT).le (by norm_num) (by norm_num : (4e-10 : ℝ) ≤ 0.00002 ^ 2)
  have s7 := sqrt_le_of (f7_set2 hT).le (by norm_num) (by norm_num : (2.01e-9 : ℝ) ≤ 0.000044834 ^ 2)
  have hsum : (√(fK aK cK T 1.00013) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2 ≤
      (0.787283939 + 0.00002 + 0.000044834) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hpi : 1 / π ≤ 1 / 3.14159265358979323846 :=
    one_div_le_one_div_of_le (by norm_num) Real.pi_gt_d20.le
  calc 1 / π * (√(fK aK cK T 1.00013) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2
      ≤ 1 / 3.14159265358979323846 * (0.787283939 + 0.00002 + 0.000044834) ^ 2 :=
        mul_le_mul hpi hsum (by positivity) (by norm_num)
    _ < 0.1973261 := by norm_num

/-! ### QUESTION: the printed bounds for `f₁`, p. 372, fail at the lower ends of the ranges -/

theorem f1_ge_main {T : ℝ} (hT : 7.02 < T) : 504 / (T * Real.log T) ≤ f1 T := by
  unfold f1
  have h0 : 0 < T := by linarith
  have hd : 0 < 1 - 7.02 / T := by rw [sub_pos, div_lt_one h0]; exact hT
  have hd1 : 1 - 7.02 / T ≤ 1 := by have : 0 ≤ 7.02 / T := by positivity
                                    linarith
  have : 1 ≤ (1 / (1 - 7.02 / T)) ^ 2 := one_le_pow₀ (by rw [le_div_iff₀ hd]; linarith)
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have : 0 ≤ 504 / (T * Real.log T) := by positivity
  nlinarith

/-- QUESTION, p. 372: the paper prints `f₁(T) < 10^{-22}` for `T ≥ e^{51}`, but
`f₁(e^{51}) > 7 · 10^{-22}`. Harmless: `f₁ < 10^{-21}` still gives `f < 0.66614`. -/
theorem f1_exp51_gt : (1e-22 : ℝ) < f1 (Real.exp 51) := by
  have h := f1_ge_main (T := Real.exp 51) (by linarith [exp51_ge])
  rw [Real.log_exp] at h
  have : (1e-22 : ℝ) < 504 / (Real.exp 51 * 51) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [exp51_le]
  linarith

/-- QUESTION, p. 372: the paper prints `f₁(T) < 10^{-36474}` for `T ≥ e^{83970}`, but
`f₁(e^{83970}) > 10^{-36474}`; the true order is `10^{-36469.9}`. Harmless. -/
theorem f1_exp83970_gt : (10 : ℝ) ^ (-36474 : ℤ) < f1 (Real.exp 83970) := by
  have h := f1_ge_main (T := Real.exp 83970)
    (by have : Real.exp 51 ≤ Real.exp 83970 := Real.exp_le_exp.2 (by norm_num)
        linarith [exp51_ge])
  rw [Real.log_exp] at h
  have : (10 : ℝ) ^ (-36474 : ℤ) < 504 / (Real.exp 83970 * 83970) := by
    rw [lt_div_iff₀ (by positivity)]
    have := exp83970_le
    calc (10 : ℝ) ^ (-36474 : ℤ) * (Real.exp 83970 * 83970)
        ≤ (10 : ℝ) ^ (-36474 : ℤ) * ((10 : ℝ) ^ 36468 * 83970) := by gcongr
      _ = 83970 / 10 ^ 6 := by
        rw [zpow_neg, zpow_ofNat, show 36474 = 36468 + 6 by norm_num, pow_add]
        field_simp
      _ < 504 := by norm_num
  linarith


end LeanLab.Kaniecki1995

#print axioms LeanLab.Kaniecki1995.acK_eq
#print axioms LeanLab.Kaniecki1995.exp_neg_cK_le
#print axioms LeanLab.Kaniecki1995.exp_neg_acK_le
#print axioms LeanLab.Kaniecki1995.T_facts
#print axioms LeanLab.Kaniecki1995.sig_facts
#print axioms LeanLab.Kaniecki1995.f1_le
#print axioms LeanLab.Kaniecki1995.f2_lt
#print axioms LeanLab.Kaniecki1995.f5_lt
#print axioms LeanLab.Kaniecki1995.f3_le
#print axioms LeanLab.Kaniecki1995.f3_set1
#print axioms LeanLab.Kaniecki1995.f3_set2
#print axioms LeanLab.Kaniecki1995.beta_bounds
#print axioms LeanLab.Kaniecki1995.f4_le
#print axioms LeanLab.Kaniecki1995.f6_le
#print axioms LeanLab.Kaniecki1995.f7_le
#print axioms LeanLab.Kaniecki1995.f1_set1
#print axioms LeanLab.Kaniecki1995.f4_set1
#print axioms LeanLab.Kaniecki1995.f6_set1
#print axioms LeanLab.Kaniecki1995.f7_set1
#print axioms LeanLab.Kaniecki1995.fK_set1
#print axioms LeanLab.Kaniecki1995.Jconst_set1
#print axioms LeanLab.Kaniecki1995.exp83970_ge
#print axioms LeanLab.Kaniecki1995.exp83970_le
#print axioms LeanLab.Kaniecki1995.f1_set2
#print axioms LeanLab.Kaniecki1995.f4_set2
#print axioms LeanLab.Kaniecki1995.f6_set2
#print axioms LeanLab.Kaniecki1995.f7_set2
#print axioms LeanLab.Kaniecki1995.fK_set2
#print axioms LeanLab.Kaniecki1995.Jconst_set2
#print axioms LeanLab.Kaniecki1995.f1_exp51_gt
#print axioms LeanLab.Kaniecki1995.f1_exp83970_gt
