import LeanLab.Halupczok2012.Progression398

/-!
Halupczok journal pages 343 to 345, the variable residue binary reduction.
The U1439 proof is reused with the arbitrary residue overlap moment.
All constants are chosen before the residue function.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Variable398

open Finset
open scoped Classical

/-- The binary error reduction, uniformly in the residue chosen for each modulus.
Source: page 344 display 4.2 and the maximum supplement on page 345.
This is conditional only on Theorem5. -/
theorem binaryPart_uniform (h5 : Theorem5) : ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 →
    ∀ B : ℝ, 0 < B → ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∃ C Y0 : ℝ,
    ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 → Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
      ∀ a : ℕ → ℤ, ∑ q ∈ Icc 1 ⌊Q⌋₊, |binPart n X1 Y1 X2 Y2 q (a q)| ≤ C * Y1 * Y2 * Real.log Y2 ^ (-A) := by
  intro A ε ε1 ε2 hA hε hε1 hε2 B hB c hc
  have c0 := hc 0; have c1 := hc 1; have c2 := hc 2; have c3 := hc 3
  have c4 := hc 4; have c5 := hc 5; have c6 := hc 6
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈c 3⌉₊ + 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hc3m : c 3 ≤ m := by
    have := Nat.le_ceil (c 3); rw [hmdef]; push_cast; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  obtain ⟨C5, Y05, h5'⟩ := h5 (2 * A + 5) ε ε2 (by linarith) hε hε2 (c 1) (c 2 / (2 * m))
    (c 3 + 1) (c 4 / 2) (c 5 + c 3 + 3) c1 (by positivity) (by linarith)
    (by linarith) (by linarith)
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = (c 3 / c 0) ^ 2 + c 3 + (1 / c 1) ^ 2 + 1 + c 5 := ⟨_, rfl⟩
  have hK0pos : 0 < K0 := by rw [hK0]; positivity
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = |Real.log K0| + 2 := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = |Real.log (c 6 ^ 2 * c 3)| + 2 := ⟨_, rfl⟩
  have hK2nn : 0 ≤ K2 := by rw [hK2]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = K1 ^ 2 * max C5 0 * (K2 ^ 3 + c 6 ^ 2) := ⟨_, rfl⟩
  have hKnn : 0 ≤ K := by
    rw [hK]; have := le_max_right C5 0; positivity
  refine ⟨Real.sqrt K, max Y05 (max (Real.exp 1) (max 4 (4 / c 4))), ?_⟩
  intro n X1 Y1 X2 Y2 Q hY1 hY2 hH a
  obtain ⟨hn, hYX1, h0, hYX2, h1, h2, h3, hD0, hD1, hD2, hQ1, hQ2⟩ := hH
  have hY05 : Y05 ≤ Y2 := le_trans (le_max_left _ _) hY2
  have hYe : Real.exp 1 ≤ Y2 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY2
  have hY4 : 4 ≤ Y2 := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hY2
  have hY4c : 4 / c 4 ≤ Y2 := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hY2
  have hY14 : 4 ≤ Y1 := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hY1
  have hc4Y : 4 ≤ c 4 * Y2 := by
    have := mul_le_mul_of_nonneg_left hY4c c4.le
    rwa [mul_div_cancel₀ _ c4.ne'] at this
  have hL1 : 1 ≤ Real.log Y2 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hYe
  have hL0 : 0 < Real.log Y2 := by linarith
  have hX1 : 4 ≤ X1 := by linarith
  have hX2 : 4 ≤ X2 := by linarith
  -- the size of `n`
  have hX1sq : X1 ≤ (Y1 / c 0) ^ 2 := le_sq_of_rpow c0 (by linarith) (by linarith) h0
  have hX2sq : X2 ≤ (Y2 / c 1) ^ 2 := le_sq_of_rpow c1 (by linarith) (by linarith) h1
  have hnpos : (0 : ℝ) < n := by linarith
  have hnK : (n : ℝ) ≤ K0 * Y2 ^ 2 := by
    have e1 : (Y1 / c 0) ^ 2 ≤ (c 3 / c 0) ^ 2 * Y2 ^ 2 := by
      rw [div_pow, div_pow, div_mul_eq_mul_div, ← mul_pow]
      gcongr
    have e2 : (Y2 / c 1) ^ 2 = (1 / c 1) ^ 2 * Y2 ^ 2 := by ring
    have hYY : Y2 ≤ Y2 ^ 2 := by rw [sq]; exact le_mul_of_one_le_right (by linarith) (by linarith)
    have e3 : c 3 * Y2 ≤ c 3 * Y2 ^ 2 := mul_le_mul_of_nonneg_left hYY c3.le
    have e4 : c 5 * Y2 ≤ c 5 * Y2 ^ 2 := mul_le_mul_of_nonneg_left hYY c5.le
    have e5 : K0 * Y2 ^ 2 = (c 3 / c 0) ^ 2 * Y2 ^ 2 + c 3 * Y2 ^ 2 + (1 / c 1) ^ 2 * Y2 ^ 2 +
        Y2 ^ 2 + c 5 * Y2 ^ 2 := by rw [hK0]; ring
    rw [e5]
    linarith
  have hlogn : Real.log n ≤ K1 * Real.log Y2 := by
    have h := Real.log_le_log hnpos hnK
    rw [Real.log_mul hK0pos.ne' (by positivity), Real.log_pow] at h
    have := le_abs_self (Real.log K0)
    have : K1 * Real.log Y2 = |Real.log K0| * Real.log Y2 + 2 * Real.log Y2 := by
      rw [hK1]; ring
    have : |Real.log K0| ≤ |Real.log K0| * Real.log Y2 := by
      exact le_mul_of_one_le_right (abs_nonneg _) hL1
    push_cast at h
    linarith
  -- `Q`
  have hQ0 : 0 ≤ Q := by linarith
  have hQnQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0
  have hQn1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ1)
  have hQn1R : (1 : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast hQn1
  have hLB : Real.log Y2 ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hX1pos : 0 < X1 := by linarith
  have hsq : Real.sqrt X1 ^ 2 = X1 := Real.sq_sqrt hX1pos.le
  have hsqpos : 0 < Real.sqrt X1 := Real.sqrt_pos.mpr hX1pos
  have hQs : Q * Real.sqrt X1 ≤ c 6 * Y1 := by
    have e : X1 ^ (-(1 / 2) : ℝ) = (Real.sqrt X1)⁻¹ := by
      rw [Real.rpow_neg hX1pos.le, Real.sqrt_eq_rpow]
    rw [e] at hQ2
    have hnn : 0 ≤ c 6 * Y1 * (Real.sqrt X1)⁻¹ := by positivity
    have : Q ≤ c 6 * Y1 * (Real.sqrt X1)⁻¹ := by
      calc Q ≤ c 6 * Y1 * (Real.sqrt X1)⁻¹ * Real.log Y2 ^ (-B) := hQ2
        _ ≤ c 6 * Y1 * (Real.sqrt X1)⁻¹ * 1 := mul_le_mul_of_nonneg_left hLB hnn
        _ = _ := mul_one _
    rw [← le_div_iff₀ hsqpos]; rwa [div_eq_mul_inv]
  have hQsq : Q ^ 2 ≤ c 6 ^ 2 * Y1 := by
    have h' : Q ^ 2 * X1 ≤ c 6 ^ 2 * Y1 ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hQs 2
      rw [mul_pow, hsq, mul_pow] at this; exact this
    have hYY : c 6 ^ 2 * Y1 ^ 2 ≤ c 6 ^ 2 * Y1 * X1 := by
      have : Y1 ^ 2 ≤ Y1 * X1 := by rw [sq]; exact mul_le_mul_of_nonneg_left hYX1 (by linarith)
      have := mul_le_mul_of_nonneg_left this (sq_nonneg (c 6))
      linarith
    have : Q ^ 2 * X1 ≤ (c 6 ^ 2 * Y1) * X1 := by linarith
    exact le_of_mul_le_mul_right this hX1pos
  have hQnsq : ((⌊Q⌋₊ : ℕ) : ℝ) ^ 2 ≤ c 6 ^ 2 * Y1 :=
    le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hQnQ 2) hQsq
  have hHb : 1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ≤ K2 * Real.log Y2 := by
    have hb : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ c 6 ^ 2 * c 3 * Y2 := by
      have e1 : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) ^ 2 := by
        rw [sq]; exact le_mul_of_one_le_right (by linarith) hQn1R
      have e2 : c 6 ^ 2 * Y1 ≤ c 6 ^ 2 * (c 3 * Y2) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      linarith
    have h := Real.log_le_log (by linarith) hb
    rw [Real.log_mul (by positivity) (by linarith)] at h
    have := le_abs_self (Real.log (c 6 ^ 2 * c 3))
    have : K2 * Real.log Y2 = |Real.log (c 6 ^ 2 * c 3)| * Real.log Y2 + 2 * Real.log Y2 := by
      rw [hK2]; ring
    have : |Real.log (c 6 ^ 2 * c 3)| ≤ |Real.log (c 6 ^ 2 * c 3)| * Real.log Y2 := by
      exact le_mul_of_one_le_right (abs_nonneg _) hL1
    linarith
  have hH0 : 0 ≤ 1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ) := one_add_log_nonneg _
  -- the window and the weights
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ,
      w = fun p : ℕ => Real.log p * (binSum X2 Y2 (n - p) - S (n - p) * Y2) := ⟨_, rfl⟩
  have hrw : ∀ q, binPart n X1 Y1 X2 Y2 q (a q) =
      ∑ p ∈ (P1w n X1 Y1).filter (fun p : ℕ => (p : ℤ) ≡ a q [ZMOD q]), w p := by
    intro q; rw [binPart, P1_eq_filter, hw]
  simp_rw [hrw]
  have hCS := Progression398.residue_cauchy (P1w n X1 Y1) w ⌊Q⌋₊ a
  have hWin : ∀ p ∈ P1w n X1 Y1, X1 < p ∧ (p : ℝ) ≤ X1 + Y1 := by
    intro p hp
    simp only [P1w, Finset.mem_filter] at hp
    exact ⟨hp.2.2.1, hp.2.2.2⟩
  have hDm := Progression398.residue_moment (by linarith) hWin ⌊Q⌋₊ a
  have hDm' : ∑ m ∈ P1w n X1 Y1, (((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℝ) ^ 2 ≤
      Y1 * (K2 ^ 3 + c 6 ^ 2) * Real.log Y2 ^ 3 := by
    have e1 : (1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ)) ^ 3 ≤ (K2 * Real.log Y2) ^ 3 :=
      pow_le_pow_left₀ hH0 hHb 3
    have hL3 : 1 ≤ Real.log Y2 ^ 3 := one_le_pow₀ hL1
    have e2 : Y1 * (1 + Real.log ((⌊Q⌋₊ : ℕ) : ℝ)) ^ 3 ≤ Y1 * (K2 * Real.log Y2) ^ 3 :=
      mul_le_mul_of_nonneg_left e1 (by linarith)
    have e3 : c 6 ^ 2 * Y1 ≤ c 6 ^ 2 * Y1 * Real.log Y2 ^ 3 := by
      have : 0 ≤ c 6 ^ 2 * Y1 := by positivity
      exact le_mul_of_one_le_right this hL3
    have e4 : Y1 * (K2 ^ 3 + c 6 ^ 2) * Real.log Y2 ^ 3 =
        Y1 * (K2 * Real.log Y2) ^ 3 + c 6 ^ 2 * Y1 * Real.log Y2 ^ 3 := by ring
    rw [e4]
    linarith
  -- the weights: Theorem 5 on `m` pieces
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun r : ℕ => (binSum X2 Y2 r - S r * Y2) ^ 2 := ⟨_, rfl⟩
  have hbnn : ∀ r, 0 ≤ b r := by intro r; rw [hb]; exact sq_nonneg _
  obtain ⟨Xb, hXb⟩ : ∃ Xb : ℝ, Xb = ((n : ℝ) - X1 - Y1) / 2 - 1 := ⟨_, rfl⟩
  obtain ⟨Rb, hRb⟩ : ∃ Rb : ℝ, Rb = Y1 / 2 + 1 := ⟨_, rfl⟩
  have hRb0 : 0 < Rb := by rw [hRb]; linarith
  have hRbY : Rb ≤ Y1 := by rw [hRb]; linarith
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = Rb / m := ⟨_, rfl⟩
  have hR'0 : 0 < R' := by rw [hR']; exact div_pos hRb0 hmpos
  have hmR' : (m : ℝ) * R' = Rb := by rw [hR']; field_simp
  have hR'le : R' ≤ Rb := by rw [hR']; exact div_le_self hRb0.le hmR
  have hR'Y : R' ≤ Y2 / 2 + 1 := by
    rw [hR', div_le_iff₀ hmpos, hRb]
    have : Y1 ≤ m * Y2 := le_trans h3 (mul_le_mul_of_nonneg_right hc3m (by linarith))
    linarith
  have hpiece : ∀ j ∈ range m, ∑ k ∈ kRange (Xb + j * R') R', b (2 * k) ≤
      C5 * R' * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5)) := by
    intro j hj
    have hjm : (j : ℝ) + 1 ≤ m := by
      have := Finset.mem_range.mp hj; exact_mod_cast this
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjR : (j : ℝ) * R' ≤ Rb := by
      rw [← hmR']; exact mul_le_mul_of_nonneg_right (by linarith) hR'0.le
    have hjR0 : 0 ≤ (j : ℝ) * R' := by positivity
    have e2X : 2 * (Xb + j * R') - X2 - Y2 =
        ((n : ℝ) - X1 - Y1 - X2 - Y2) - 2 + 2 * (j * R') := by
      rw [hXb]; ring
    have hXbge : R' ≤ Xb := by rw [hXb]; linarith
    rw [hb]
    apply h5' (Xb + j * R') X2 Y2 R' hY05 h1 hYX2
    · -- lower bound for `R'`
      rw [hR', hRb]
      have : c 2 / (2 * m) * Y2 ^ (1 / 3 + ε) = (c 2 * Y2 ^ (1 / 3 + ε) / 2) / m := by
        field_simp
      rw [this]
      apply div_le_div_of_nonneg_right _ hmpos.le
      linarith
    · have := mul_nonneg c3.le (by linarith : (0 : ℝ) ≤ Y2); linarith
    · linarith
    · rw [e2X]; linarith
    · rw [e2X]; linarith
    · rw [e2X]; rw [hRb] at hjR; linarith
  have hLp : 0 ≤ Real.log Y2 ^ (-(2 * A + 5)) := Real.rpow_nonneg hL0.le _
  have hbsum : ∑ k ∈ kRange Xb Rb, b (2 * k) ≤
      max C5 0 * Y1 * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5)) := by
    have hcov := sum_kRange_le_pieces Xb Rb hRb0 m hm0 (fun k => b (2 * k)) (fun k => hbnn _)
    rw [← hR'] at hcov
    have hsum := Finset.sum_le_sum hpiece
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have e : (m : ℝ) * (C5 * R' * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5))) =
        C5 * Rb * (Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5))) := by rw [← hmR']; ring
    have hC : C5 * Rb ≤ max C5 0 * Y1 := by
      calc C5 * Rb ≤ max C5 0 * Rb := mul_le_mul_of_nonneg_right (le_max_left _ _) hRb0.le
        _ ≤ max C5 0 * Y1 := mul_le_mul_of_nonneg_left hRbY (le_max_right _ _)
    have hP : 0 ≤ Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5)) := mul_nonneg (sq_nonneg _) hLp
    have := mul_le_mul_of_nonneg_right hC hP
    have e2 : max C5 0 * Y1 * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5)) =
        max C5 0 * Y1 * (Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5))) := by ring
    rw [e2]
    linarith
  have hwsum : ∑ p ∈ P1w n X1 Y1, w p ^ 2 ≤
      (K1 * Real.log Y2) ^ 2 * (max C5 0 * Y1 * Y2 ^ 2 * Real.log Y2 ^ (-(2 * A + 5))) := by
    have hlog : ∀ p ∈ P1w n X1 Y1, Real.log p ^ 2 ≤ (K1 * Real.log Y2) ^ 2 := by
      intro p hp
      simp only [P1w, Finset.mem_filter, Finset.mem_range] at hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.1.one_lt.le
      have hpn : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
      have h0' : 0 ≤ Real.log p := Real.log_nonneg hp1
      have := Real.log_le_log (by linarith) hpn
      have : Real.log p ≤ K1 * Real.log Y2 := by linarith
      exact pow_le_pow_left₀ h0' this 2
    have hP1 := sum_P1w_le n X1 Y1 hn (by linarith) b hbnn
    rw [← hXb, ← hRb] at hP1
    calc ∑ p ∈ P1w n X1 Y1, w p ^ 2 = ∑ p ∈ P1w n X1 Y1, Real.log p ^ 2 * b (n - p) := by
          apply Finset.sum_congr rfl; intro p _; rw [hw, hb]; ring
      _ ≤ ∑ p ∈ P1w n X1 Y1, (K1 * Real.log Y2) ^ 2 * b (n - p) := by
          apply Finset.sum_le_sum; intro p hp
          exact mul_le_mul_of_nonneg_right (hlog p hp) (hbnn _)
      _ = (K1 * Real.log Y2) ^ 2 * ∑ p ∈ P1w n X1 Y1, b (n - p) := by rw [Finset.mul_sum]
      _ ≤ (K1 * Real.log Y2) ^ 2 * ∑ k ∈ kRange Xb Rb, b (2 * k) :=
          mul_le_mul_of_nonneg_left hP1 (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbsum (sq_nonneg _)
  -- assemble
  have hS0 : 0 ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊,
      |∑ p ∈ (P1w n X1 Y1).filter (fun p : ℕ => (p : ℤ) ≡ a q [ZMOD q]), w p| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hLA : 0 ≤ Real.log Y2 ^ (-A) := Real.rpow_nonneg hL0.le (-A)
  have hM : 0 ≤ Y1 * Y2 * Real.log Y2 ^ (-A) := by
    have : 0 ≤ Y1 * Y2 := mul_nonneg (by linarith) (by linarith)
    exact mul_nonneg this hLA
  have hfin : (∑ q ∈ Icc 1 ⌊Q⌋₊,
      |∑ p ∈ (P1w n X1 Y1).filter (fun p : ℕ => (p : ℤ) ≡ a q [ZMOD q]), w p|) ^ 2 ≤
      K * (Y1 * Y2 * Real.log Y2 ^ (-A)) ^ 2 := by
    have hDnn : 0 ≤ ∑ m ∈ P1w n X1 Y1, (((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hR1 : 0 ≤ (K1 * Real.log Y2) ^ 2 * (max C5 0 * Y1 * Y2 ^ 2 *
        Real.log Y2 ^ (-(2 * A + 5))) := by
      have := le_max_right C5 0
      have : 0 ≤ Y1 := by linarith
      positivity
    calc _ ≤ (∑ p ∈ P1w n X1 Y1, w p ^ 2) *
          ∑ m ∈ P1w n X1 Y1, (((Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => (m : ℤ) ≡ a q [ZMOD q])).card : ℝ) ^ 2 := hCS
      _ ≤ ((K1 * Real.log Y2) ^ 2 * (max C5 0 * Y1 * Y2 ^ 2 *
            Real.log Y2 ^ (-(2 * A + 5)))) * (Y1 * (K2 ^ 3 + c 6 ^ 2) * Real.log Y2 ^ 3) :=
          mul_le_mul hwsum hDm' hDnn hR1
      _ = K * (Y1 * Y2) ^ 2 * (Real.log Y2 ^ 2 * Real.log Y2 ^ 3 *
            Real.log Y2 ^ (-(2 * A + 5))) := by rw [hK]; ring
      _ = K * (Y1 * Y2 * Real.log Y2 ^ (-A)) ^ 2 := by rw [log_pow_identity hL0]; ring
  have := Real.sqrt_le_sqrt hfin
  rw [Real.sqrt_sq hS0, Real.sqrt_mul hKnn, Real.sqrt_sq hM] at this
  calc _ ≤ Real.sqrt K * (Y1 * Y2 * Real.log Y2 ^ (-A)) := this
    _ = Real.sqrt K * Y1 * Y2 * Real.log Y2 ^ (-A) := by ring

/-- Halupczok page 344, separate the binary fluctuation from the singular series main term. -/
theorem error_split (n : ℕ) (X1 Y1 X2 Y2 : ℝ) (q : ℕ) (a : ℤ) :
    ternSum n X1 Y1 X2 Y2 q a - T n q a * Y1 * Y2 =
      binPart n X1 Y1 X2 Y2 q a + Y2 * (mainSum n X1 Y1 q a - T n q a * Y1) := by
  rw [ternSum_eq, binPart, mainSum]
  have he : (∑ p ∈ P1 n X1 Y1 q a, Real.log p * binSum X2 Y2 (n - p)) =
      (∑ p ∈ P1 n X1 Y1 q a, Real.log p * (binSum X2 Y2 (n - p) - S (n - p) * Y2)) +
      Y2 * ∑ p ∈ P1 n X1 Y1 q a, Real.log p * S (n - p) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    ring
  rw [he]
  ring

end LeanLab.Halupczok2012.Variable398
