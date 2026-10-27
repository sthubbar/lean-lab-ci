import LeanLab.LiuWang2002.Vaughan109
import LeanLab.LiuWang2002.Decomp109b

/-! Proposition 6.1, pages 168 to 174. AI wrote the Lean code.
Binary Goldbach is open. Analytic leaves remain CONDITIONAL. -/

namespace LeanLab.LiuWang2002.Decomp109

open Real Vaughan109

/-- First scale in display 6.2, page 168. -/
noncomputable def A (N q : ℝ) : ℝ := N * q ^ (-(1 / 2) : ℝ) * log N ^ 2
/-- Second scale in display 6.2, page 168. -/
noncomputable def B (N : ℝ) : ℝ := N ^ (4 / 5 : ℝ) * log N ^ (1.4 : ℝ)
/-- Third scale in display 6.2, page 168. -/
noncomputable def C (N q : ℝ) : ℝ := N ^ (1 / 2 : ℝ) * q ^ (1 / 2 : ℝ) * log N ^ (2.5 : ℝ)

/-- CITED. Proposition 6.1, displays 6.1 and 6.2, page 168.
Every real N at least 3 and every fixed c in the open unit interval are allowed. -/
def VinogradovEstimate : Prop :=
  ∀ (N c : ℝ), 3 ≤ N → 0 < c → c < 1 →
    ∀ (a : ℤ) (q : ℕ), 1 ≤ q → a.natAbs.Coprime q →
      ∀ θ : ℝ, |θ| ≤ 1 →
        ‖S N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)‖ ≤
          0.28 * A N q + 4 * B N + 0.09 * C N q

/-- LEAF. Crude estimate preceding display 6.3, page 168.
External input: Rosser and Schoenfeld 1962, display 3.6. -/
theorem crude (N c α : ℝ) (hN : 3 ≤ N) (hc : 0 < c) (hc1 : c < 1) :
    ‖S N c α‖ ≤ 1.25506 * N := by
  sorry

/-- LEAF. Refined estimate preceding display 6.3, page 168.
External input: Rosser and Schoenfeld 1975, page 265, displays 5.1 and 5.3. -/
theorem refined (N c α : ℝ) (hN : 6.36e12 ≤ N) (hc : 0 < c) (hc1 : c < 1) :
    ‖S N c α‖ ≤ 1.0012 * N := by
  have hcut : exp 9.634 ≤ (6.36e12 : ℝ) := by
    apply (le_log_iff_exp_le (by norm_num)).mp
    linarith [Numeric109.log_cutoff_lower]
  exact (Decomp109b.full_triangle N c α (by linarith)).trans
    ((Decomp109b.psi_bound N (hcut.trans hN)).trans (Decomp109b.refined_roots N hN))

/-- LEAF. Small N reduction on page 168 before display 6.3. -/
theorem small_N (N : ℝ) (hN : 3 ≤ N) (hsmall : N < 6.36e12) :
    1.25506 * N ≤ 4 * B N := by
  have hNp : 0 < N := by linarith
  have he : exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
  have hL : 1 ≤ log N := (le_log_iff_exp_le hNp).mpr (he.le.trans hN)
  have hLp : 0 < log N := by linarith
  have hpow : N ≤ (4 / 1.25506) ^ 5 * log N ^ 7 := by
    by_cases h5 : log N ≤ 5
    · have he5 : exp (5 : ℝ) ≤ 3 ^ 5 := by
        have hh := pow_le_pow_left₀ (exp_pos 1).le he.le 5
        have heq : exp (5 : ℝ) = exp 1 ^ 5 := by simpa using exp_nat_mul (1 : ℝ) 5
        rwa [← heq] at hh
      have hn : N ≤ 3 ^ 5 := by
        calc N = exp (log N) := (exp_log hNp).symm
          _ ≤ exp 5 := exp_le_exp.mpr h5
          _ ≤ _ := he5
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL 7
      norm_num at hh ⊢
      nlinarith
    by_cases h7 : log N ≤ 7
    · have he7 : exp (7 : ℝ) ≤ 3 ^ 7 := by
        have hh := pow_le_pow_left₀ (exp_pos 1).le he.le 7
        have heq : exp (7 : ℝ) = exp 1 ^ 7 := by simpa using exp_nat_mul (1 : ℝ) 7
        rwa [← heq] at hh
      have hn : N ≤ 3 ^ 7 := by
        calc N = exp (log N) := (exp_log hNp).symm
          _ ≤ exp 7 := exp_le_exp.mpr h7
          _ ≤ _ := he7
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) (le_of_not_ge h5) 7
      norm_num at hh ⊢
      nlinarith
    have hT : 0 < log (6.36e12 : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 29.481)
      Numeric109.log_cutoff_lower
    have hr := Numeric109.exp_div_pow7_mono (log N) (log (6.36e12 : ℝ))
      (le_of_not_ge h7) (log_le_log hNp hsmall.le)
    rw [exp_log hNp, exp_log (by norm_num : (0 : ℝ) < 6.36e12)] at hr
    have ht : (6.36e12 : ℝ) / log (6.36e12 : ℝ) ^ 7 ≤ (4 / 1.25506) ^ 5 := by
      apply (div_le_iff₀ (pow_pos hT 7)).mpr
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 29.481) Numeric109.log_cutoff_lower 7
      norm_num at hh ⊢
      nlinarith
    exact (div_le_iff₀ (pow_pos hLp 7)).mp (hr.trans ht)
  have e1 : (N ^ (4 / 5 : ℝ)) ^ 5 = N ^ 4 := by
    rw [← rpow_natCast _ 5, ← rpow_mul hNp.le]
    norm_num
  have e2 : (log N ^ (1.4 : ℝ)) ^ 5 = log N ^ 7 := by
    rw [← rpow_natCast _ 5, ← rpow_mul hLp.le]
    norm_num
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ 1.25506 * N)
    (by unfold B; positivity : 0 ≤ 4 * B N) (show (5 : ℕ) ≠ 0 by decide)).mp
  unfold B
  rw [mul_pow, mul_pow, mul_pow, e1, e2]
  have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ N ^ 4 by positivity)
  nlinarith

/-- LEAF. Numerical reduction 6.3 to 6.5, page 168.
Only the middle term is needed to infer the lower bound for N. -/
theorem large_N (N : ℝ) (hN : 6.36e12 ≤ N) (hB : 4 * B N < 1.0012 * N) :
    exp 30.95 ≤ N := by
  have hNp : 0 < N := by linarith
  have hL := Numeric109.log_ge_seven N hN
  have hLp : 0 < log N := by linarith
  have e1 : (N ^ (4 / 5 : ℝ)) ^ 5 = N ^ 4 := by
    rw [← rpow_natCast _ 5, ← rpow_mul hNp.le]
    norm_num
  have e2 : (log N ^ (1.4 : ℝ)) ^ 5 = log N ^ 7 := by
    rw [← rpow_natCast _ 5, ← rpow_mul hLp.le]
    norm_num
  have hp := pow_lt_pow_left₀ hB (show 0 ≤ 4 * B N by unfold B; positivity)
    (show (5 : ℕ) ≠ 0 by decide)
  unfold B at hp
  rw [mul_pow, mul_pow, e1, e2, mul_pow] at hp
  have hn : (4 / 1.0012) ^ 5 * log N ^ 7 < N := by
    by_contra hno
    have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hno) (show 0 ≤ N ^ 4 by positivity)
    nlinarith
  by_contra hno
  have ht : log N ≤ 30.95 := (log_lt_iff_lt_exp hNp).mpr (lt_of_not_ge hno) |>.le
  have hr := Numeric109.exp_div_pow7_mono (log N) 30.95 hL ht
  rw [exp_log hNp] at hr
  have he : exp 30.95 / 30.95 ^ 7 < (4 / 1.0012) ^ 5 := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 30.95 ^ 7)).mpr
    exact Constants.prop61_N_lower
  have hh := (div_lt_iff₀ (pow_pos hLp 7)).mp (hr.trans_lt he)
  linarith

/-- LEAF. Lemma 6.2, page 169, with the inclusive cutoff of display 3.8.
External input: the Rosser and Schoenfeld estimate for psi used in the printed proof. -/
theorem first_sum (N c α : ℝ) (hN : exp 30.95 ≤ N) (hc : 0 < c) (hc1 : c < 1) :
    ‖S1 N c α‖ ≤ 1.02 * U N :=
  Decomp109b.lemma62 N c α hN hc hc1

/-- LEAF. The unused coefficient margin in the assembly on page 174. -/
theorem first_absorb (N : ℝ) (hN : exp 30.95 ≤ N) :
    1.02 * U N ≤ 0.4129 * B N := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hL1 : 1 ≤ log N := by linarith
  have hN1 : 1 ≤ N := by
    have := Real.add_one_le_exp (30.95 : ℝ)
    linarith
  have hp := rpow_le_rpow_of_exponent_le hN1 (show (2 / 5 : ℝ) ≤ 4 / 5 by norm_num)
  have hl := rpow_le_one_of_one_le_of_nonpos hL1 (show (-(4 / 5) : ℝ) ≤ 0 by norm_num)
  have hb : 3 ≤ log N ^ (1.4 : ℝ) := by
    have hh := rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 1.4 by norm_num)
    rw [rpow_one] at hh
    linarith
  have hu : U N ≤ N ^ (4 / 5 : ℝ) := by
    unfold U
    exact (mul_le_mul_of_nonneg_left hl (rpow_nonneg hNp.le _)).trans (by simpa using hp)
  have hn0 := rpow_nonneg hNp.le (4 / 5 : ℝ)
  have hh := mul_le_mul_of_nonneg_left hb hn0
  unfold B
  nlinarith

/-- LEAF. Lemma 6.5, pages 169 and 170, in the nontrivial regime of page 168.
External input: Wang and Chen 1994 Lemma 3, quoted as Lemma 6.4.
The inclusive cutoff of display 3.8 is retained. -/
theorem second_sum (N c : ℝ) (a : ℤ) (q : ℕ) (θ : ℝ)
    (hN : exp 30.95 ≤ N) (hc : 0 < c) (hc1 : c < 1)
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hθ : |θ| ≤ 1)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    ‖S2 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)‖ ≤
      0.0282 * A N q + 0.0001 * B N + 0.0006 * C N q := by
  sorry

/-- LEAF. Lemma 6.6, page 170, in the nontrivial regime of page 168.
External input: Wang and Chen 1994 Lemma 3, quoted as Lemma 6.4.
The inclusive cutoff of display 3.8 is retained. -/
theorem third_sum (N c : ℝ) (a : ℤ) (q : ℕ) (θ : ℝ)
    (hN : exp 30.95 ≤ N) (hc : 0 < c) (hc1 : c < 1)
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hθ : |θ| ≤ 1)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    ‖S3 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)‖ ≤
      0.0131 * A N q + 0.8 * B N + 0.0005 * C N q := by
  sorry

/-- LEAF. Lemma 6.7, pages 170 to 174, in the nontrivial regime of page 168.
External inputs: Wang and Chen 1994 Lemma 2 and Rosser and Schoenfeld 1962.
The inclusive cutoff of display 3.8 is retained. -/
theorem fourth_sum (N c : ℝ) (a : ℤ) (q : ℕ) (θ : ℝ)
    (hN : exp 30.95 ≤ N) (hc : 0 < c) (hc1 : c < 1)
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hθ : |θ| ≤ 1)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    ‖S4 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)‖ ≤
      0.2264 * A N q + 2.787 * B N + 0.0785 * C N q := by
  sorry

/-- Proposition 6.1, page 174. CONDITIONAL ON the named analytic leaves.
The assembly has exactly the CITED proposition as its type. -/
theorem proposition61 : VinogradovEstimate := by
  intro N c hN hc hc1 a q hq hcop θ hθ
  have hNp : 0 ≤ N := by linarith
  have hlog : 0 ≤ log N := Real.log_nonneg (by linarith)
  have hAn : 0 ≤ A N q := by unfold A; positivity
  have hBn : 0 ≤ B N := by unfold B; positivity
  have hCn : 0 ≤ C N q := by unfold C; positivity
  by_cases hs : N < 6.36e12
  · have h := (crude N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2) hN hc hc1).trans (small_N N hN hs)
    linarith
  have hr := refined N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2) (le_of_not_gt hs) hc hc1
  by_cases ha : 1.0012 * N ≤ 0.28 * A N q
  · linarith
  by_cases hb : 1.0012 * N ≤ 4 * B N
  · linarith
  by_cases hd : 1.0012 * N ≤ 0.09 * C N q
  · linarith
  have hn := large_N N (le_of_not_gt hs) (lt_of_not_ge hb)
  have h1 := (first_sum N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2) hn hc hc1).trans (first_absorb N hn)
  have h2 := second_sum N c a q θ hn hc hc1 hq hcop hθ (lt_of_not_ge ha) (lt_of_not_ge hd)
  have h3 := third_sum N c a q θ hn hc hc1 hq hcop hθ (lt_of_not_ge ha) (lt_of_not_ge hd)
  have h4 := fourth_sum N c a q θ hn hc hc1 hq hcop hθ (lt_of_not_ge ha) (lt_of_not_ge hd)
  rw [vaughan_sum]
  have ht := norm_add_le (S1 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2) + S2 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)) (S3 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2))
  have ht' := norm_add_le (S1 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)) (S2 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2))
  have ht'' := norm_add_le
    (S1 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2) + S2 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2) + S3 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)) (S4 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2))
  linarith

end LeanLab.LiuWang2002.Decomp109

#print axioms LeanLab.LiuWang2002.Decomp109.proposition61

#print axioms LeanLab.LiuWang2002.Decomp109.first_absorb
#print axioms LeanLab.LiuWang2002.Decomp109.large_N

#print axioms LeanLab.LiuWang2002.Decomp109.small_N

#print axioms LeanLab.LiuWang2002.Decomp109.first_sum

#print axioms LeanLab.LiuWang2002.Decomp109.refined
