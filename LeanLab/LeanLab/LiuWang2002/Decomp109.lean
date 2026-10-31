import LeanLab.LiuWang2002.Vaughan109
import LeanLab.LiuWang2002.Decomp109b
import LeanLab.ChebyshevExplicit.Psi30Upper
import LeanLab.LiuWang2002.Decomp1543c

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

/-- Error absorption for the crude estimate before display 6.3 on page 168.
The threshold 4096 is an internal bound for the existing Chebyshev estimate. -/
theorem task194_crude_error (X : ℝ) (hX : 4096 ≤ X) :
    2 * log X ^ 2 + 160 ≤ 0.14886 * X := by
  have hX0 : 0 < X := by linarith
  have hs : (64 : ℝ) ≤ √X := (Real.le_sqrt (by norm_num) hX0.le).mpr (by nlinarith)
  have hs0 : 0 < √X := by linarith
  have hh := Real.log_le_sub_one_of_pos (show 0 < √X / 64 by positivity)
  rw [Real.log_div hs0.ne' (by norm_num), Real.log_sqrt hX0.le] at hh
  have h64 : log (64 : ℝ) ≤ 4.2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have hL : log X ≤ √X / 5 := by linarith
  have hL0 : 0 ≤ log X := Real.log_nonneg (by linarith)
  have hsq := pow_le_pow_left₀ hL0 hL 2
  have hs2 := Real.sq_sqrt hX0.le
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Initial range certificate for the crude estimate on page 168.
Together with the analytic bound above 4096 this closes every natural input. -/
theorem task194_lcm_certificate :
    ∀ n ∈ Finset.range 4096, Nat.lcmUpto n ≤ 2 ^ (9 * n / 5) := by
  have hb : (∀ n ∈ Finset.range 64, Nat.lcmUpto n ≤ 2 ^ (9 * n / 5)) ∧
      (∀ d ∈ ({8, 16, 32, 64, 128, 256} : Finset ℕ), ∀ k ∈ Finset.Icc 8 15,
        Nat.lcmUpto (d * (k + 1)) ≤ 2 ^ (9 * (d * k) / 5)) := by
    decide +kernel
  intro n hn
  by_cases hs : n < 64
  · exact hb.1 n (Finset.mem_range.mpr hs)
  have hn' := Finset.mem_range.mp hn
  have hcover : ∃ d ∈ ({8, 16, 32, 64, 128, 256} : Finset ℕ),
      8 * d ≤ n ∧ n < 16 * d := by
    have hh : n < 128 ∨ (128 ≤ n ∧ n < 256) ∨ (256 ≤ n ∧ n < 512) ∨
        (512 ≤ n ∧ n < 1024) ∨ (1024 ≤ n ∧ n < 2048) ∨ (2048 ≤ n ∧ n < 4096) := by omega
    rcases hh with h | h | h | h | h | h
    all_goals first
      | exact ⟨8, by norm_num, by omega⟩
      | exact ⟨16, by norm_num, by omega⟩
      | exact ⟨32, by norm_num, by omega⟩
      | exact ⟨64, by norm_num, by omega⟩
      | exact ⟨128, by norm_num, by omega⟩
      | exact ⟨256, by norm_num, by omega⟩
  obtain ⟨d, hd, hlo, hhi⟩ := hcover
  have hd0 : 0 < d := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hk : n / d ∈ Finset.Icc 8 15 := by
    simp only [Finset.mem_Icc]
    constructor
    · exact (Nat.le_div_iff_mul_le hd0).mpr hlo
    · have h := (Nat.div_lt_iff_lt_mul hd0).mpr hhi
      omega
  have hnm : n ≤ d * (n / d + 1) := (Nat.lt_mul_div_succ n hd0).le
  have hdvd : Nat.lcmUpto n ∣ Nat.lcmUpto (d * (n / d + 1)) := by
    apply Finset.lcm_mono
    intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hnm⟩
  have hm : d * (n / d) ≤ n := Nat.mul_div_le n d
  exact (Nat.le_of_dvd (Nat.lcmUpto_pos _) hdvd).trans
    ((hb.2 d hd _ hk).trans (Nat.pow_le_pow_right (by decide) (Nat.div_le_div_right (by omega))))

/-- The global psi bound used before display 6.3 on page 168.
This proof uses the lab Chebyshev estimate and an initial range certificate. -/
theorem task194_psi_crude (n : ℕ) : Chebyshev.psi n ≤ 1.25506 * n := by
  by_cases hn : n < 4096
  · have hc := task194_lcm_certificate n (Finset.mem_range.mpr hn)
    have hcR : (Nat.lcmUpto n : ℝ) ≤ 2 ^ (9 * n / 5) := by exact_mod_cast hc
    have hh := Real.log_le_log (by exact_mod_cast Nat.lcmUpto_pos n) hcR
    rw [Real.log_pow] at hh
    rw [Chebyshev.psi_eq_log_lcmUpto]
    have hf : ((9 * n / 5 : ℕ) : ℝ) * 5 ≤ 9 * n := by
      exact_mod_cast Nat.div_mul_le_self (9 * n) 5
    have hm := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le
      (show (0 : ℝ) ≤ (9 * n / 5 : ℕ) by positivity)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  · have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast (by omega : 4096 ≤ n)
    have h := LeanLab.ChebyshevExplicit.psi_le_11062 n
    have he := task194_crude_error n hnR
    linarith

/-- LEAF. Crude estimate preceding display 6.3, page 168.
External input: Rosser and Schoenfeld 1962, display 3.6. -/
theorem crude (N c α : ℝ) (hN : 3 ≤ N) (hc : 0 < c) (hc1 : c < 1) :
    ‖S N c α‖ ≤ 1.25506 * N := by
  have hN0 : 0 ≤ N := by linarith
  have hp : (∑ n ∈ Finset.range (Nat.floor N + 1), ArithmeticFunction.vonMangoldt n) =
      Chebyshev.psi (Nat.floor N) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp [Nat.range_succ_eq_Icc_zero, Nat.floor_natCast]
  have hfloor := Nat.floor_le hN0
  exact (Decomp109b.full_triangle N c α hN0).trans
    (hp ▸ (task194_psi_crude (Nat.floor N)).trans (by nlinarith))

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

/-- Exact conversion of the inclusive cutoff in display 3.8 on page 144
to a strict cutoff for display 6.8 on page 169. -/
theorem task194_sum_transfer (f : ArithmeticFunction ℝ) (N c α : ℝ) (hN : 1 ≤ N) (hc : 0 < c) :
    weightedSum f N c α =
      U1543.Ssum (fun n => f n) (((⌈c * N⌉₊ : ℝ) - 1) / ⌊N⌋₊) ⌊N⌋₊ α := by
  have hNp : (0 : ℝ) < N := by linarith
  have hcutp : 0 < c * N := mul_pos hc hNp
  have hf : 0 < ⌊N⌋₊ := Nat.floor_pos.mpr hN
  have hfR : (⌊N⌋₊ : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have hcut (n : ℕ) : c * N ≤ (n : ℝ) ↔ (⌈c * N⌉₊ : ℝ) - 1 < n := by
    rw [← Nat.ceil_le]
    have : ((⌈c * N⌉₊ : ℕ) ≤ n) ↔ ((⌈c * N⌉₊ : ℝ) ≤ n) := by exact_mod_cast Iff.rfl
    rw [this]
    constructor
    · intro h; linarith
    · intro h
      have h' : (⌈c * N⌉₊ : ℝ) < (n : ℝ) + 1 := by linarith
      have h'' : ⌈c * N⌉₊ < n + 1 := by exact_mod_cast h'
      exact_mod_cast (show ⌈c * N⌉₊ ≤ n by omega)
  unfold weightedSum U1543.Ssum U1543.rangeN
  rw [Finset.sum_filter]
  have hs : Finset.Icc 1 ⌊N⌋₊ ⊆ Finset.range (⌊N⌋₊ + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
  symm
  apply (Finset.sum_subset hs ?_).trans
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [div_mul_cancel₀ _ hfR, ← hcut n, U1543.e, Complex.ofReal_mul, Complex.ofReal_natCast]
  · intro n hn hnot
    have hn0 : n = 0 := by
      have := Finset.mem_range.mp hn
      simp only [Finset.mem_Icc, not_and] at hnot
      omega
    subst n
    rw [ite_eq_right (by
      rw [div_mul_cancel₀ _ hfR]
      have hceil : 1 ≤ ⌈c * N⌉₊ := Nat.ceil_pos.mpr hcutp
      have hceilR : (1 : ℝ) ≤ ⌈c * N⌉₊ := by exact_mod_cast hceil
      norm_num only [Nat.cast_zero] at *
      linarith)]

open U1543 ArithmeticFunction Finset in
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta in
/-- The convolution coefficients equal the divisor coefficients in display 6.8
on page 169 for every natural index. -/
theorem task194_coefficients (U V : ℝ) (n : ℕ) :
    lambda2 V n = lam2 V n ∧ lambda3 U V n = lam3 U V n ∧ lambda4 U V n = lam4 U V n := by
  classical
  have hl (f : ArithmeticFunction ℝ) (X : ℝ) (k : ℕ) :
      longPart f X k = if X < (k : ℝ) then f k else 0 := by
    change f k - (if (k : ℝ) ≤ X then f k else 0) = _
    split_ifs <;> simp_all; linarith
  have h2 : lambda2 V n = lam2 V n := by
    unfold lambda2 lam2
    rw [mul_apply, Nat.sum_divisorsAntidiagonal
      (fun x y => (shortPart (μ : ArithmeticFunction ℝ) V) x * ArithmeticFunction.log y),
      sum_filter]
    apply sum_congr rfl
    intro t ht
    simp [shortPart, ite_mul]
  have h4 : lambda4 U V n = lam4 U V n := by
    unfold lambda4 lam4
    rw [mul_apply, Nat.sum_divisorsAntidiagonal
      (fun x y => (longPart (μ : ArithmeticFunction ℝ) V) x *
        (longPart Λ U * (ζ : ArithmeticFunction ℝ)) y), sum_filter]
    apply sum_congr rfl
    intro t ht
    rw [hl, coe_mul_zeta_apply]
    simp only [hl, am, sum_filter]
    split_ifs <;> simp_all
  have h3 : lambda3 U V n = lam3 U V n := by
    unfold lambda3 lam3
    rw [ArithmeticFunction.neg_apply, mul_assoc, mul_apply, Nat.sum_divisorsAntidiagonal
      (fun x y => (shortPart Λ U) x *
        (shortPart (μ : ArithmeticFunction ℝ) V * (ζ : ArithmeticFunction ℝ)) y)]
    congr 1
    apply sum_congr rfl
    intro r hr
    rw [coe_mul_zeta_apply, mul_sum]
    have hrn := Nat.dvd_of_mem_divisors hr
    have hn0 := Nat.ne_zero_of_mem_divisors hr
    have hr0 := Nat.pos_of_mem_divisors hr
    have hnr0 : n / r ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by omega) hrn) hr0)
    have hset : (n / r).divisors = n.divisors.filter (fun t => r * t ∣ n) := by
      ext t
      simp only [Nat.mem_divisors, mem_filter]
      constructor
      · rintro ⟨ht, _⟩
        have hrt : r * t ∣ n := (Nat.dvd_div_iff_mul_dvd hrn).1 ht
        exact ⟨⟨(dvd_mul_left t r).trans hrt, hn0⟩, hrt⟩
      · rintro ⟨⟨ht, _⟩, hrt⟩
        refine ⟨?_, hnr0⟩
        apply (Nat.dvd_div_iff_mul_dvd hrn).2
        simpa [mul_comm] using hrt
    rw [hset, sum_filter]
    apply sum_congr rfl
    intro t ht
    simp only [shortPart, coe_mk, intCoe_apply]
    split_ifs <;> simp_all
  exact ⟨h2, h3, h4⟩

/-- Exact logarithms of U and V for positive real N in display 6.6 on page 168. -/
theorem task194_logs (N : ℝ) (hNpos : 0 < N) (hL : 30.95 ≤ Real.log N) :
    0 < (N : ℝ) ∧ 0 < U N ∧ 0 < V N ∧
    Real.log (U N) = 2 / 5 * Real.log N - 4 / 5 * Real.log (Real.log N) ∧
    Real.log (V N) = 2 / 5 * Real.log N + 1 / 5 * Real.log (Real.log N) := by
  have hN : (0 : ℝ) < N := hNpos
  have hL0 : 0 < Real.log N := by linarith
  have hp := Real.rpow_pos_of_pos hN ((2 : ℝ) / 5)
  have hU : 0 < U N := mul_pos hp (Real.rpow_pos_of_pos hL0 _)
  have hV : 0 < V N := mul_pos hp (Real.rpow_pos_of_pos hL0 _)
  refine ⟨hN, hU, hV, ?_, ?_⟩
  · unfold U
    rw [Real.log_mul hp.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hN,
      Real.log_rpow hL0]
    ring
  · unfold V
    rw [Real.log_mul hp.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hN,
      Real.log_rpow hL0]

/-- The denominator range of display 6.3 implies 15 at most q at most N on page 168. -/
theorem task194_q_range (N : ℝ) (hNpos : 0 < N) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) : 15 ≤ q ∧ (q : ℝ) ≤ N := by
  have h4 : (30.95 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have h5 : (30.95 : ℝ) ^ 5 ≤ Real.log N ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
  have hL5 : (0 : ℝ) < Real.log N ^ 5 := by positivity
  constructor
  · have : (15 : ℝ) < q := by nlinarith
    exact_mod_cast this.le
  · have hN : (0 : ℝ) ≤ N := hNpos.le
    have : (1.0012 / 0.09) ^ 2 * (N : ℝ) / Real.log N ^ 5 ≤ N := by
      rw [div_le_iff₀ hL5]; nlinarith
    exact_mod_cast (hq2.trans_le this).le

/-- The printed upper bound for log q in the proof of Lemma 6.5 on page 170. -/
theorem task194_q_log_upper (N : ℝ) (q : ℕ) (hNpos : 0 < N) (hL : 30.95 ≤ Real.log N)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Real.log q ≤ Real.log N - 12.34 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [Nat.cast_zero, Real.log_zero]
    linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < N := hNpos
  have hL0 : 0 < Real.log N := by linarith
  have he : exp (12.34 : ℝ) ≤ (2.7182818286 : ℝ) ^ 12 * 1.405 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 12
    have he12 : exp (12 : ℝ) = exp 1 ^ 12 := by simpa using Real.exp_nat_mul (1 : ℝ) 12
    have hr : exp (0.34 : ℝ) ≤ 1.405 := by
      have hh := Real.exp_bound' (x := (0.34 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at hh
      linarith
    rw [show (12.34 : ℝ) = 12 + 0.34 by norm_num, Real.exp_add, he12]
    exact mul_le_mul hp hr (Real.exp_pos _).le (by positivity)
  have hc : (1.0012 / 0.09) ^ 2 * exp (12.34 : ℝ) ≤ Real.log N ^ 5 := by
    have hp : (30.95 : ℝ) ^ 5 ≤ Real.log N ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
    calc
      _ ≤ (1.0012 / 0.09) ^ 2 * ((2.7182818286 : ℝ) ^ 12 * 1.405) := by gcongr
      _ ≤ (30.95 : ℝ) ^ 5 := by norm_num
      _ ≤ _ := hp
  have hdiv : (1.0012 / 0.09) ^ 2 / Real.log N ^ 5 ≤ exp (-12.34 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_div_iff₀ (pow_pos hL0 5) (Real.exp_pos _)).mpr
    simpa only [one_mul] using hc
  have hqN : (q : ℝ) ≤ (N : ℝ) * exp (-12.34 : ℝ) := by
    calc
      _ ≤ (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5 := hq2.le
      _ = N * ((1.0012 / 0.09) ^ 2 / Real.log N ^ 5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv hN0.le
  have hh := Real.log_le_log hq0 hqN
  rw [Real.log_mul hN0.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
  linarith

/-- The reciprocal denominator term in Lemma 6.5 on page 170 for real N. -/
theorem task194_n65c (N : ℝ) (hNpos : 0 < N) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (V N) * Real.log N ≤ 0.0282 * N / √q * Real.log N ^ 2 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task194_logs N hNpos hL
  have hL0 : 0 < Real.log N := by linarith
  have hlogL := Real.log_le_sub_one_of_pos hL0
  have hlv1 : Real.log (V N) ≤ Real.log N := by rw [hlv]; linarith
  have h4 : (30.95 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hqbig : (250 : ℝ) ≤ √q := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg q)).mpr
    nlinarith
  have hsq : (√(q : ℝ)) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hq0 : (0 : ℝ) < q := by nlinarith [Real.sqrt_nonneg (q : ℝ)]
  have hs0 : (0 : ℝ) < √q := by linarith
  calc
    _ ≤ 5 * N / q * Real.log N * Real.log N := by gcongr
    _ = ((N : ℝ) / √q * Real.log N ^ 2) * (5 / √q) := by
      field_simp
      nlinarith [hsq]
    _ ≤ ((N : ℝ) / √q * Real.log N ^ 2) * 0.0282 := by
      gcongr
      apply (div_le_iff₀ hs0).mpr
      linarith
    _ = _ := by ring

/-- The reciprocal denominator term in Lemma 6.6 on page 170 for real N. -/
theorem task194_n66c (N : ℝ) (hNpos : 0 < N) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (U N * V N) * Real.log (U N * V N) ≤
      0.0131 * N / √q * Real.log N ^ 2 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task194_logs N hNpos hL
  have hL0 : 0 < Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hL1
  have hlogLupper := Real.log_le_sub_one_of_pos hL0
  have huv0 : 0 ≤ Real.log (U N * V N) := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have huv : Real.log (U N * V N) ≤ 0.8 * Real.log N := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have h4 : (30.95 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hqbig : (250 : ℝ) ≤ √q := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg q)).mpr
    nlinarith
  have hsq : (√(q : ℝ)) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hq0 : (0 : ℝ) < q := by nlinarith [Real.sqrt_nonneg (q : ℝ)]
  have hs0 : (0 : ℝ) < √q := by linarith
  calc
    _ ≤ 5 * N / q * (0.8 * Real.log N) * (0.8 * Real.log N) := by gcongr
    _ = ((N : ℝ) / √q * Real.log N ^ 2) * (3.2 / √q) := by
      field_simp
      nlinarith [hsq]
    _ ≤ ((N : ℝ) / √q * Real.log N ^ 2) * 0.0131 := by
      gcongr
      apply (div_le_iff₀ hs0).mpr
      linarith
    _ = _ := by ring

/-- The q and q log q terms in Lemma 6.5 on page 170 for real N. -/
theorem task194_n65a (N : ℝ) (hNpos : 0 < N) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log N ≤
      0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hq15, hqN⟩ := task194_q_range N hNpos hL q hq1 hq2
  have hL0 : 0 < Real.log N := by linarith
  have hlq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg _
  have hupper := task194_q_log_upper N q hNpos hL hq2
  have hfirst : 5 + 1.5 * Real.log q ≤ 1.5 * Real.log N := by linarith
  have hpl : (Real.log N ^ (2.5 : ℝ)) ^ 2 = Real.log N ^ 5 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hL0.le]
    norm_num
  have hs : √(q : ℝ) * Real.log N ^ (2.5 : ℝ) ≤ (1.0012 / 0.09) * √N := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg q), Real.sq_sqrt (hNpos.le), hpl]
    exact ((lt_div_iff₀ (pow_pos hL0 5)).mp hq2).le
  have h3 : 1.5 * (1.0012 / 0.09) ≤ 0.0006 * Real.log N ^ 3 := by
    have hh : (30.95 : ℝ) ^ 3 ≤ Real.log N ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
    nlinarith
  have hc : (1.0012 / 0.09) * (1.5 * Real.log N) * Real.log N ≤ 0.0006 * Real.log N ^ 5 := by
    have hm := mul_le_mul_of_nonneg_right h3 (sq_nonneg (Real.log N))
    nlinarith
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hL0 (2.5 : ℝ))).mp
  calc
    _ = √(q : ℝ) * (√q * Real.log N ^ (2.5 : ℝ)) *
        (5 + 1.5 * Real.log q) * Real.log N := by
      ring_nf
      rw [Real.sq_sqrt (Nat.cast_nonneg q)]
      ring
    _ ≤ √(q : ℝ) * ((1.0012 / 0.09) * √N) * (1.5 * Real.log N) * Real.log N := by gcongr
    _ = √(N : ℝ) * √q * ((1.0012 / 0.09) * (1.5 * Real.log N) * Real.log N) := by ring
    _ ≤ √(N : ℝ) * √q * (0.0006 * Real.log N ^ 5) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ)) * Real.log N ^ (2.5 : ℝ) := by
      rw [← hpl]
      ring
    _ = Real.log N ^ (2.5 : ℝ) * (0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ)) := by ring

/-- The V log q term in Lemma 6.5 on page 170 for real N. -/
theorem task194_n65b (N : ℝ) (hNpos : 0 < N) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    V N * Real.log q * Real.log N ≤ 0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task194_logs N hNpos hL
  have hL0 : 0 < Real.log N := by linarith
  obtain ⟨hq15, hqN⟩ := task194_q_range N hNpos hL q hq1 hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlq : Real.log q ≤ Real.log N := Real.log_le_log hq0 (by exact_mod_cast hqN)
  have hlogL : Real.log (Real.log N) ≤ 3.4325 + (Real.log N / 30.95 - 1) := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < Real.log N / 30.95 by positivity)
    rw [Real.log_div hL0.ne' (by norm_num)] at hh
    linarith [Decomp109b.log_endpoint]
  have hc : (-9.3 : ℝ) ≤ Real.log (0.0001 : ℝ) := by
    have hh : Real.log (10000 : ℝ) ≤ 9.3 := by
      have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 10000)
        (show (10000 : ℝ) ≤ (2 : ℝ) ^ 13 * 1.25 by norm_num)
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow] at ht
      norm_num only [Nat.cast_ofNat] at ht
      linarith [Real.log_two_lt_d9, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.25)]
    rw [show (0.0001 : ℝ) = (10000 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  calc
    _ ≤ V N * Real.log N ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hlq (mul_pos hV hL0).le]
    _ ≤ _ := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      rw [Real.log_mul hV.ne' (pow_pos hL0 2).ne', Real.log_pow, hlv,
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
      norm_num at hlogL ⊢
      linarith

/-- The q and q log q terms in Lemma 6.6 on page 170 for real N. -/
theorem task194_n66a (N : ℝ) (hNpos : 0 < N) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log (U N * V N) ≤
      0.0005 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task194_logs N hNpos hL
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have huv : Real.log (U N * V N) ≤ 0.8 * Real.log N := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have hq15 := (task194_q_range N hNpos hL q hq1 hq2).1
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  calc
    _ ≤ (5 * q + 1.5 * q * Real.log q) * (0.8 * Real.log N) := by gcongr
    _ = 0.8 * ((5 * q + 1.5 * q * Real.log q) * Real.log N) := by ring
    _ ≤ 0.8 * (0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ)) :=
      mul_le_mul_of_nonneg_left (task194_n65a N hNpos hL q hq1 hq2) (by norm_num)
    _ ≤ _ := by
      have h : 0 ≤ √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) := by positivity
      nlinarith

/-- The UV log q term in Lemma 6.6 on page 170 for real N. -/
theorem task194_n66b (N : ℝ) (hNpos : 0 < N) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    U N * V N * Real.log q * Real.log (U N * V N) ≤
      0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task194_logs N hNpos hL
  have hL0 : 0 < Real.log N := by linarith
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have huv : Real.log (U N * V N) ≤ 0.8 * Real.log N := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have hlogLupper := Real.log_le_sub_one_of_pos hL0
  have huv0 : 0 ≤ Real.log (U N * V N) := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  obtain ⟨hq15, hqN⟩ := task194_q_range N hNpos hL q hq1 hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlq : Real.log q ≤ Real.log N := Real.log_le_log hq0 (by exact_mod_cast hqN)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have he : U N * V N * Real.log N ^ 2 =
      (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_mul (mul_pos hU hV).ne' (pow_pos hL0 2).ne',
      Real.log_mul hU.ne' hV.ne', Real.log_pow, hlu, hlv,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
    ring
  calc
    _ ≤ U N * V N * Real.log N * (0.8 * Real.log N) := by gcongr
    _ = 0.8 * (U N * V N * Real.log N ^ 2) := by ring
    _ = _ := by rw [he]; ring

open U1543 Finset in
/-- Partial summation for the inclusive real sum in Lemma 6.5 on page 170. -/
theorem task194_S2_le (N c X α : ℝ) (hN : 1 ≤ N) (hc : 0 < c) :
    ‖weightedSum (lambda2 X) N c α‖ ≤
      Real.log N * ∑ t ∈ Icc 1 ⌊X⌋₊, minK (N / t) (α * t) := by
  have hN0 : 0 < N := by linarith
  have hf : 0 < ⌊N⌋₊ := Nat.floor_pos.mpr hN
  have hfR : (0 : ℝ) < ⌊N⌋₊ := by exact_mod_cast hf
  have hcut : 0 ≤ ((⌈c * N⌉₊ : ℝ) - 1) / ⌊N⌋₊ := by
    apply div_nonneg _ hfR.le
    have hceil : 0 < ⌈c * N⌉₊ := Nat.ceil_pos.mpr (mul_pos hc hN0)
    have hceilR : (1 : ℝ) ≤ ⌈c * N⌉₊ := by exact_mod_cast hceil
    linarith
  rw [task194_sum_transfer _ N c α hN hc]
  have heq : (fun n => lambda2 X n) = lam2 X := by
    funext n
    exact (task194_coefficients 0 X n).1
  rw [heq]
  have hb := S2_le _ hcut ⌊N⌋₊ X α
  refine hb.trans ?_
  have hl : Real.log (⌊N⌋₊ : ℝ) ≤ Real.log N := Real.log_le_log hfR (Nat.floor_le hN0.le)
  have hl0 : 0 ≤ Real.log (⌊N⌋₊ : ℝ) := Real.log_natCast_nonneg _
  have hsum : (∑ t ∈ Icc 1 ⌊X⌋₊, minK ((⌊N⌋₊ : ℝ) / t) (α * t)) ≤
      ∑ t ∈ Icc 1 ⌊X⌋₊, minK (N / t) (α * t) := by
    apply Finset.sum_le_sum
    intro t ht
    have hdiv := div_le_div_of_nonneg_right (Nat.floor_le hN0.le) (Nat.cast_nonneg t)
    unfold minK
    split_ifs <;> gcongr
  exact mul_le_mul hl hsum (by
    apply Finset.sum_nonneg
    intro t ht
    unfold minK nint
    split_ifs <;> positivity) (by linarith)

open U1543 Finset in
/-- Partial summation for the inclusive real sum in Lemma 6.6 on page 170. -/
theorem task194_S3_le (N c X Y α : ℝ) (hN : 1 ≤ N) (hc : 0 < c) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    ‖weightedSum (lambda3 X Y) N c α‖ ≤
      Real.log (X * Y) * ∑ t ∈ Icc 1 ⌊X * Y⌋₊, minK (N / t) (α * t) := by
  have hN0 : 0 < N := by linarith
  have hf : 0 < ⌊N⌋₊ := Nat.floor_pos.mpr hN
  have hfR : (0 : ℝ) < ⌊N⌋₊ := by exact_mod_cast hf
  have hcut : 0 ≤ ((⌈c * N⌉₊ : ℝ) - 1) / ⌊N⌋₊ := by
    apply div_nonneg _ hfR.le
    have hceil : 0 < ⌈c * N⌉₊ := Nat.ceil_pos.mpr (mul_pos hc hN0)
    have hceilR : (1 : ℝ) ≤ ⌈c * N⌉₊ := by exact_mod_cast hceil
    linarith
  rw [task194_sum_transfer _ N c α hN hc]
  have heq : (fun n => lambda3 X Y n) = lam3 X Y := by
    funext n
    exact (task194_coefficients X Y n).2.1
  rw [heq]
  have hb := S3_le _ hcut ⌊N⌋₊ X Y α hX hY
  refine hb.trans ?_
  have hl0 : 0 ≤ Real.log (X * Y) := Real.log_nonneg (by nlinarith)
  have hsum : (∑ t ∈ Icc 1 ⌊X * Y⌋₊, minK ((⌊N⌋₊ : ℝ) / t) (α * t)) ≤
      ∑ t ∈ Icc 1 ⌊X * Y⌋₊, minK (N / t) (α * t) := by
    apply Finset.sum_le_sum
    intro t ht
    have hdiv := div_le_div_of_nonneg_right (Nat.floor_le hN0.le) (Nat.cast_nonneg t)
    unfold minK
    split_ifs <;> gcongr
  exact mul_le_mul_of_nonneg_left hsum hl0

/-- The two nontrivial scale assumptions imply display 6.3 on page 168. -/
theorem task194_range_of_scales (N : ℝ) (q : ℕ) (hN : 0 < N) (hq : 1 ≤ q)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N)
    (hL : 0 < log N) :
    (0.28 / 1.0012) ^ 2 * log N ^ 4 < q ∧
      (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / log N ^ 5 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have hNhalf : N ^ (1 / 2 : ℝ) = √N := (Real.sqrt_eq_rpow N).symm
  have hqhalf : (q : ℝ) ^ (1 / 2 : ℝ) = √q := (Real.sqrt_eq_rpow (q : ℝ)).symm
  have hAeq : A N q = N / √q * log N ^ 2 := by
    unfold A
    rw [Real.rpow_neg hq0.le, hqhalf]
    ring
  have hCeq : C N q = √N * √q * log N ^ (2.5 : ℝ) := by
    unfold C
    rw [hNhalf, hqhalf]
  rw [hAeq] at hA
  rw [hCeq] at hC
  have ha : (0.28 / 1.0012) * log N ^ 2 < √q := by
    have hh := (div_lt_iff₀ hs).mp (show 0.28 * N * log N ^ 2 / √q < 1.0012 * N by
      convert hA using 1; ring)
    nlinarith
  have hc : 0.09 * √q * log N ^ (2.5 : ℝ) < 1.0012 * √N := by
    have hsN : 0 < √N := Real.sqrt_pos.mpr hN
    have hNN : √N * √N = N := Real.mul_self_sqrt hN.le
    nlinarith
  have ha2 := sq_lt_sq₀ (by positivity : 0 ≤ (0.28 / 1.0012) * log N ^ 2) hs.le |>.mpr ha
  have hc2 := sq_lt_sq₀ (by positivity : 0 ≤ 0.09 * √q * log N ^ (2.5 : ℝ))
    (by positivity : 0 ≤ 1.0012 * √N) |>.mpr hc
  have hp : (log N ^ (2.5 : ℝ)) ^ 2 = log N ^ 5 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hL.le]
    norm_num
  rw [mul_pow, Real.sq_sqrt hq0.le] at ha2
  simp only [mul_pow, Real.sq_sqrt hq0.le, Real.sq_sqrt hN.le, hp] at hc2
  constructor
  · nlinarith
  · apply (lt_div_iff₀ (pow_pos hL 5)).mpr
    nlinarith


/-- Lemma 6.5 on page 170 for real N and the inclusive cutoff.
CONDITIONAL ON the explicit Wang and Chen Lemma 3 hypothesis from page 169. -/
theorem task194_second_of_wc (hWC : U1543.WCLemma3) (N c : ℝ) (a : ℤ) (q : ℕ) (θ : ℝ)
    (hN : exp 30.95 ≤ N) (hc : 0 < c) (hc1 : c < 1)
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hθ : |θ| ≤ 1)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    ‖S2 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)‖ ≤
      0.0282 * A N q + 0.0001 * B N + 0.0006 * C N q := by
  let α : ℝ := (a : ℝ) / q + θ / (q : ℝ) ^ 2
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hN1 : 1 ≤ N := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 30.95)).trans hN
  have hL : 30.95 ≤ log N := (Real.le_log_iff_exp_le hNp).mpr hN
  have hLp : 0 < log N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hD : U1543.Dioph α a q := by
    refine ⟨hq, ?_, ?_⟩
    · simpa [Int.gcd_def, Nat.Coprime] using hcop
    · dsimp [α]
      simp only [add_sub_cancel_left, abs_div, abs_pow, Nat.abs_cast]
      exact div_le_div_of_nonneg_right hθ (by positivity)
  obtain ⟨hq1, hq2⟩ := task194_range_of_scales N q hNp hq hA hC hLp
  obtain ⟨_, hU0, hV0, hlu, hlv⟩ := task194_logs N hNp hL
  have hLV : 0 ≤ log (V N) := by
    rw [hlv]
    have := Real.log_nonneg (show 1 ≤ log N by linarith)
    linarith
  have hV1 : 1 ≤ V N := by
    have hh := Real.one_le_exp hLV
    rwa [Real.exp_log hV0] at hh
  have hq15 := (task194_q_range N hNp hL q hq1 hq2).1
  have hw := hWC α a q hD hq15 (V N) N hV1 hNp
  have h1 := (task194_S2_le N c (V N) α hN1 hc).trans
    (mul_le_mul_of_nonneg_left hw hLp.le)
  have e : log N * (5 * q + 1.5 * q * log q + V N * log q +
      5 * N / q * log (V N)) = (5 * q + 1.5 * q * log q) * log N +
      V N * log q * log N + 5 * N / q * log (V N) * log N := by ring
  rw [e] at h1
  have hb : ‖weightedSum (lambda2 (V N)) N c α‖ ≤
      0.0282 * N / √q * log N ^ 2 + 0.0001 * N ^ (4 / 5 : ℝ) * log N ^ (1.4 : ℝ) +
        0.0006 * √N * √q * log N ^ (2.5 : ℝ) := by
    linarith [task194_n65a N hNp hL q hq1 hq2, task194_n65b N hNp hL q hq1 hq2,
      task194_n65c N hNp hL q hq1 hq2]
  change ‖weightedSum (lambda2 (V N)) N c α‖ ≤ _
  refine hb.trans_eq ?_
  have hNhalf : N ^ (1 / 2 : ℝ) = √N := (Real.sqrt_eq_rpow N).symm
  have hqhalf : (q : ℝ) ^ (1 / 2 : ℝ) = √q := (Real.sqrt_eq_rpow (q : ℝ)).symm
  unfold A B C
  rw [Real.rpow_neg hq0.le, hqhalf, hNhalf]
  ring

/-- Lemma 6.6 on page 170 for real N and the inclusive cutoff.
CONDITIONAL ON the explicit Wang and Chen Lemma 3 hypothesis from page 169. -/
theorem task194_third_of_wc (hWC : U1543.WCLemma3) (N c : ℝ) (a : ℤ) (q : ℕ) (θ : ℝ)
    (hN : exp 30.95 ≤ N) (hc : 0 < c) (hc1 : c < 1)
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hθ : |θ| ≤ 1)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    ‖S3 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)‖ ≤
      0.0131 * A N q + 0.8 * B N + 0.0005 * C N q := by
  let α : ℝ := (a : ℝ) / q + θ / (q : ℝ) ^ 2
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hN1 : 1 ≤ N := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 30.95)).trans hN
  have hL : 30.95 ≤ log N := (Real.le_log_iff_exp_le hNp).mpr hN
  have hLp : 0 < log N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hD : U1543.Dioph α a q := by
    refine ⟨hq, ?_, ?_⟩
    · simpa [Int.gcd_def, Nat.Coprime] using hcop
    · dsimp [α]
      simp only [add_sub_cancel_left, abs_div, abs_pow, Nat.abs_cast]
      exact div_le_div_of_nonneg_right hθ (by positivity)
  obtain ⟨hq1, hq2⟩ := task194_range_of_scales N q hNp hq hA hC hLp
  obtain ⟨_, hU0, hV0, hlu, hlv⟩ := task194_logs N hNp hL
  have hLV : 0 ≤ log (V N) := by
    rw [hlv]
    have := Real.log_nonneg (show 1 ≤ log N by linarith)
    linarith
  have hV1 : 1 ≤ V N := by
    have hh := Real.one_le_exp hLV
    rwa [Real.exp_log hV0] at hh
  have hhalf := Real.log_le_sub_one_of_pos (show 0 < log N / 2 by positivity)
  rw [Real.log_div hLp.ne' (by norm_num)] at hhalf
  have hLU : 0 ≤ log (U N) := by
    rw [hlu]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hU1 : 1 ≤ U N := by
    have hh := Real.one_le_exp hLU
    rwa [Real.exp_log hU0] at hh
  have hUV1 : 1 ≤ U N * V N := by nlinarith
  have hq15 := (task194_q_range N hNp hL q hq1 hq2).1
  have hw := hWC α a q hD hq15 (U N * V N) N hUV1 hNp
  have hl0 : 0 ≤ log (U N * V N) := Real.log_nonneg hUV1
  have h1 := (task194_S3_le N c (U N) (V N) α hN1 hc hU1 hV1).trans
    (mul_le_mul_of_nonneg_left hw hl0)
  have e : log (U N * V N) * (5 * q + 1.5 * q * log q +
      U N * V N * log q + 5 * N / q * log (U N * V N)) =
      (5 * q + 1.5 * q * log q) * log (U N * V N) +
      U N * V N * log q * log (U N * V N) +
      5 * N / q * log (U N * V N) * log (U N * V N) := by ring
  rw [e] at h1
  have hb : ‖weightedSum (lambda3 (U N) (V N)) N c α‖ ≤
      0.0131 * N / √q * log N ^ 2 + 0.8 * N ^ (4 / 5 : ℝ) * log N ^ (1.4 : ℝ) +
        0.0005 * √N * √q * log N ^ (2.5 : ℝ) := by
    linarith [task194_n66a N hNp hL q hq1 hq2, task194_n66b N hNp hL q hq1 hq2,
      task194_n66c N hNp hL q hq1 hq2]
  change ‖weightedSum (lambda3 (U N) (V N)) N c α‖ ≤ _
  refine hb.trans_eq ?_
  have hNhalf : N ^ (1 / 2 : ℝ) = √N := (Real.sqrt_eq_rpow N).symm
  have hqhalf : (q : ℝ) ^ (1 / 2 : ℝ) = √q := (Real.sqrt_eq_rpow (q : ℝ)).symm
  unfold A B C
  rw [Real.rpow_neg hq0.le, hqhalf, hNhalf]
  ring

/-- LEAF. Lemma 6.5, pages 169 and 170, in the nontrivial regime of page 168.
External input: Wang and Chen 1994 Lemma 3, quoted as Lemma 6.4.
The inclusive cutoff of display 3.8 is retained. -/
theorem second_sum (N c : ℝ) (a : ℤ) (q : ℕ) (θ : ℝ)
    (hN : exp 30.95 ≤ N) (hc : 0 < c) (hc1 : c < 1)
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hθ : |θ| ≤ 1)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    ‖S2 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)‖ ≤
      0.0282 * A N q + 0.0001 * B N + 0.0006 * C N q := by
  exact task194_second_of_wc U1543.wc_lemma3 N c a q θ hN hc hc1 hq hcop hθ hA hC

/-- LEAF. Lemma 6.6, page 170, in the nontrivial regime of page 168.
External input: Wang and Chen 1994 Lemma 3, quoted as Lemma 6.4.
The inclusive cutoff of display 3.8 is retained. -/
theorem third_sum (N c : ℝ) (a : ℤ) (q : ℕ) (θ : ℝ)
    (hN : exp 30.95 ≤ N) (hc : 0 < c) (hc1 : c < 1)
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hθ : |θ| ≤ 1)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    ‖S3 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)‖ ≤
      0.0131 * A N q + 0.8 * B N + 0.0005 * C N q := by
  exact task194_third_of_wc U1543.wc_lemma3 N c a q θ hN hc hc1 hq hcop hθ hA hC

/-- The lower bound for V used in display 6.20 on page 173,
from the full parameter range of displays 6.5 and 6.6 on page 168. -/
theorem task194_V_lower (N : ℝ) (hN : exp 30.95 ≤ N) : exp 13.066 ≤ V N := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hLp : 0 < log N := by linarith
  have he : exp (3.43 : ℝ) ≤ (30.95 : ℝ) := by
    have hp := pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le 3
    have he3 : exp (3 : ℝ) = exp 1 ^ 3 := by simpa using Real.exp_nat_mul (1 : ℝ) 3
    have hr : exp (0.43 : ℝ) ≤ 1.538 := by
      have hh := Real.exp_bound' (x := (0.43 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at hh
      linarith
    rw [show (3.43 : ℝ) = 3 + 0.43 by norm_num, Real.exp_add, he3]
    have hh := mul_le_mul hp hr (exp_pos _).le (by positivity : 0 ≤ (2.7182818286 : ℝ) ^ 3)
    norm_num at hh ⊢
    linarith
  have hLL : 3.43 ≤ log (log N) := (le_log_iff_exp_le hLp).mpr (he.trans hL)
  have hp : 0 < N ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hq : 0 < log N ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hLp _
  apply (le_log_iff_exp_le (mul_pos hp hq)).mp
  rw [Real.log_mul hp.ne' hq.ne', Real.log_rpow hNp, Real.log_rpow hLp]
  linarith

open U1543 Finset in
/-- The finite bound from displays 6.11 and 6.12 on pages 170 and 171,
with the squarefree count from display 6.20 on page 173. -/
noncomputable def fourthEnergyBound (n : ℕ) (u v : ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Jn n u v),
    √(0.6111 * (2 ^ j * v)) *
      √(((((⌊(n : ℝ) / (2 ^ j * v)⌋₊ - ⌊u⌋₊) / q : ℕ) : ℝ) + 1) *
        (5 * (2 ^ j * v + 1 / 2) + q * Real.log q) *
          ∑ m ∈ lRange n u ((n : ℝ) / (2 ^ j * v)), am u m ^ 2)

open U1543 Finset in
/-- The inclusive real fourth sum is bounded by the finite block energy.
CONDITIONAL ON the explicit Wang and Chen Lemma 2 hypothesis on page 169. -/
theorem task194_fourth_energy (hWC : WCLemma2) (N c u v α : ℝ) (a : ℤ) (q : ℕ)
    (hN : 1 ≤ N) (hc : 0 < c) (hu : 0 < u) (hv : exp 13.066 ≤ v)
    (hD : Dioph α a q) :
    ‖weightedSum (lambda4 u v) N c α‖ ≤ fourthEnergyBound ⌊N⌋₊ u v q := by
  have hv0 : 0 < v := (Real.exp_pos _).trans_le hv
  rw [task194_sum_transfer _ N c α hN hc]
  have heq : (fun n => lambda4 u v n) = lam4 u v := by
    funext n
    exact (task194_coefficients u v n).2.2
  rw [heq, S4_dyadic _ ⌊N⌋₊ u v α hu hv0]
  unfold fourthEnergyBound
  apply norm_sum_le_of_le
  intro j hj
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hvM : v ≤ 2 ^ j * v := by nlinarith
  exact task181_block_energy hWC _ ⌊N⌋₊ u (2 ^ j * v) α hu.le (hv.trans hvM) a q hD

/-- The full real parameter range of display 6.6 on page 168
and the prime power comparison on page 171. -/
theorem task194_full_params (N : ℝ) (hN : exp 30.95 ≤ N) :
    15000 ≤ U N ∧ exp 13.066 ≤ V N ∧ U N * V N ≤ N ∧ N / V N ≤ (U N) ^ 2 := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hLp : 0 < log N := by linarith
  obtain ⟨_, hU, hV, hlu, hlv⟩ := task194_logs N hNp hL
  have hLL0 : 0 ≤ log (log N) := log_nonneg (by linarith)
  refine ⟨Constants.exp9634_ge.trans (Decomp109b.U_lower N hN), task194_V_lower N hN, ?_, ?_⟩
  · apply (Real.log_le_log_iff (mul_pos hU hV) hNp).mp
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  · have ht := Real.log_le_sub_one_of_pos (show 0 < log N / 30.95 by positivity)
    rw [Real.log_div hLp.ne' (by norm_num)] at ht
    have he := Decomp109b.log_endpoint
    apply (Real.log_le_log_iff (div_pos hNp hV) (pow_pos hU 2)).mp
    rw [Real.log_div hNp.ne' hV.ne', Real.log_pow, hlu, hlv]
    norm_num at ht ⊢
    linarith

open Finset in
/-- The explicit logarithmic bound for the arithmetic energy from displays
6.13 to 6.17 on pages 171 and 172, before constant absorption. -/
noncomputable def amEnergyEnvelope (u X : ℝ) : ℝ :=
  X * ((Real.log X ^ 2 - Real.log u ^ 2) / 2 + 0.105 * Real.log X +
    Real.log X ^ 2 / √u +
      2 * (Real.log X ^ 2 / u * ∑ k ∈ Icc 2 ⌊Real.log X / Real.log 2⌋₊, (1 : ℝ) / k))
open U1543 Finset in
/-- The arithmetic energy estimate before the uniform ratio step on page 173.
CONDITIONAL ON the explicit Rosser and Schoenfeld prime sum bounds on page 172. -/
theorem task194_am_energy (n : ℕ) (u X : ℝ) (hu : 1 ≤ u) (hUX : u ≤ X) (hXu : X ≤ u ^ 2)
    (hMR : ∀ x : ℝ, u ≤ x → x ≤ X →
      Real.log x - 1.385 ≤ primeLogSum x ∧ primeLogSum x ≤ Real.log x - 1.28) :
    Wsum n u X ≤ amEnergyEnvelope u X := by
  have hX : 1 ≤ X := hu.trans hUX
  have hw := task141_W_reduction n u X hu hX hXu
  have hw1 := W1_le u X 1.385 1.28 hu hUX hMR
  unfold amEnergyEnvelope
  apply hw.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ X)
  linarith

open U1543 Finset in
/-- The dyadic energy bound with the explicit logarithmic envelope
from displays 6.13 to 6.17 on pages 171 and 172. -/
noncomputable def fourthLogBound (n : ℕ) (u v : ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Jn n u v),
    √(0.6111 * (2 ^ j * v)) *
      √(((((⌊(n : ℝ) / (2 ^ j * v)⌋₊ - ⌊u⌋₊) / q : ℕ) : ℝ) + 1) *
        (5 * (2 ^ j * v + 1 / 2) + q * Real.log q) *
          amEnergyEnvelope u ((n : ℝ) / (2 ^ j * v)))

open U1543 Finset in
/-- Each dyadic arithmetic energy is bounded by its logarithmic envelope.
CONDITIONAL ON the explicit Rosser and Schoenfeld input on page 172. -/
theorem task194_fourth_envelope (hMR : ∀ x : ℝ, 15000 ≤ x →
      Real.log x - 1.385 ≤ primeLogSum x ∧ primeLogSum x ≤ Real.log x - 1.28)
    (N : ℝ) (q : ℕ) (hN : exp 30.95 ≤ N) :
    fourthEnergyBound ⌊N⌋₊ (U N) (V N) q ≤ fourthLogBound ⌊N⌋₊ (U N) (V N) q := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  obtain ⟨hU15, hV13, hUV, hNVU⟩ := task194_full_params N hN
  have hV0 : 0 < V N := (exp_pos _).trans_le hV13
  unfold fourthEnergyBound fourthLogBound
  apply sum_le_sum
  intro j hj
  let M : ℝ := 2 ^ j * V N
  let X : ℝ := (⌊N⌋₊ : ℝ) / M
  let G : ℝ := ((((⌊X⌋₊ - ⌊U N⌋₊) / q : ℕ) : ℝ) + 1) *
    (5 * (M + 1 / 2) + q * Real.log q)
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hVM : V N ≤ M := by dsimp [M]; nlinarith
  have hM0 : 0 < M := hV0.trans_le hVM
  have hG0 : 0 ≤ G := by
    dsimp [G]
    have := Real.log_natCast_nonneg q
    positivity
  have hXupper : X ≤ N / V N := by
    dsimp [X]
    exact (div_le_div_of_nonneg_right (Nat.floor_le hNp.le) hM0.le).trans
      (div_le_div_of_nonneg_left hNp.le hV0 hVM)
  change √(0.6111 * M) * √(G * Wsum ⌊N⌋₊ (U N) X) ≤
    √(0.6111 * M) * √(G * amEnergyEnvelope (U N) X)
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  by_cases hUX : U N ≤ X
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ hG0
    exact task194_am_energy ⌊N⌋₊ (U N) X (by linarith) hUX (hXupper.trans hNVU)
      (fun x hx _ => hMR x (hU15.trans hx))
  · have hW : Wsum ⌊N⌋₊ (U N) X = 0 := by
      unfold Wsum
      apply sum_eq_zero
      intro m hm
      simp only [lRange, mem_filter, mem_Icc] at hm
      have := hm.2.1
      have := hm.2.2
      exfalso
      linarith
    rw [hW, mul_zero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _

open Finset in
/-- A derived square root sum bound for the retained dyadic endpoints
of display 6.10 on page 170 and the summation behind display 6.22 on page 174. -/
theorem task194_affine_roots (J : ℕ) (D h : ℝ) (hn : ∀ j ∈ range J, 0 ≤ D - j * h) :
    (∑ j ∈ range J, √(D - j * h)) ^ 2 ≤
      (J : ℝ) * ((J : ℝ) * D - h * ((J : ℝ) * (J - 1)) / 2) := by
  have hid (K : ℕ) : (∑ j ∈ range K, (j : ℝ)) = (K : ℝ) * (K - 1) / 2 := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  have he : (∑ j ∈ range J, (√(D - j * h)) ^ 2) =
      (J : ℝ) * D - h * ((J : ℝ) * (J - 1)) / 2 := by
    calc
      _ = ∑ j ∈ range J, (D - j * h) := by
        apply sum_congr rfl
        intro j hj
        exact Real.sq_sqrt (hn j hj)
      _ = _ := by
        rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_mul, hid]
        ring
  simpa only [card_range, he] using
    (sq_sum_le_card_mul_sum_sq (s := range J) (f := fun j => √(D - j * h)))

open Finset in
/-- A derived square root sum bound for the retained dyadic endpoints
of display 6.10 on page 170 and the summation behind display 6.22 on page 174. -/
theorem task194_weighted_roots (K : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ k ∈ range K, √(k + 1 : ℕ) * r ^ (k + 1) ≤
      r * (2 - r) / (2 * (1 - r) ^ 2) := by
  have hnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hg := hasSum_geometric_of_norm_lt_one hnorm
  have hc := hasSum_choose_mul_geometric_of_norm_lt_one 1 hnorm
  have hs : HasSum (fun k : ℕ => ((k : ℝ) + 2) / 2 * r ^ (k + 1))
      (r * (2 - r) / (2 * (1 - r) ^ 2)) := by
    convert (hc.add hg).mul_left (r / 2) using 1
    · funext k
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    · have hne : 1 - r ≠ 0 := by linarith
      norm_num only [Nat.reduceAdd] 
      field_simp
      ring
  calc
    _ ≤ ∑ k ∈ range K, ((k : ℝ) + 2) / 2 * r ^ (k + 1) := by
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
      have hp := Real.sqrt_nonneg ((k + 1 : ℕ) : ℝ)
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (k + 1 : ℕ) by positivity)
      push_cast at hp hsq ⊢
      nlinarith [sq_nonneg (√((k + 1 : ℕ) : ℝ) - 1)]
    _ ≤ _ := by
      rw [← hs.tsum_eq]
      exact Summable.sum_le_tsum (range K) (fun k hk => by positivity) hs.summable

open Finset in
/-- A derived elementary estimate for the retained dyadic energies
in the full parameter range of pages 168 to 174. -/
lemma task194_loglog_bound (L : ℝ) (hL : 30.95 ≤ L) : log L ≤ 0.112 * L := by
  have hLp : 0 < L := by linarith
  have hh := log_le_sub_one_of_pos (show 0 < L / 30.95 by positivity)
  rw [Real.log_div hLp.ne' (by norm_num)] at hh
  have he := Decomp109b.log_endpoint
  norm_num at hh
  linarith

open Finset in
/-- A derived elementary estimate for the retained dyadic energies
in the full parameter range of pages 168 to 174. -/
lemma task194_U_quadratic (N : ℝ) (hN : exp 30.95 ≤ N) : 9 * log N ^ 2 ≤ U N := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hLp : 0 < log N := by linarith
  obtain ⟨_, hU, hV, hlu, hlv⟩ := task194_logs N hNp hL
  have h9 : log (9 : ℝ) ≤ 2.4 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    rw [log_div (by norm_num) (by norm_num)] at hh
    have he : log (9 : ℝ) = 2 * log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  apply (Real.log_le_log_iff (by positivity : 0 < 9 * log N ^ 2) hU).mp
  rw [Real.log_mul (by norm_num) (pow_pos hLp 2).ne', Real.log_pow, hlu]
  norm_num
  linarith [task194_loglog_bound (log N) hL]

open Finset in
/-- A derived elementary estimate for the retained dyadic energies
in the full parameter range of pages 168 to 174. -/
lemma task194_density_profile (N X : ℝ) (hN : exp 30.95 ≤ N) (hUX : U N ≤ X) (hXV : X ≤ N / V N) :
    amEnergyEnvelope (U N) X ≤ X * (0.5 * log N * log (X / U N) + 0.192 * log N) := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hLp : 0 < log N := by linarith
  obtain ⟨_, hU, hV, hlu, hlv⟩ := task194_logs N hNp hL
  obtain ⟨hU15, _, _, _⟩ := task194_full_params N hN
  have hX : 0 < X := hU.trans_le hUX
  have hLX0 : 0 ≤ log X := log_nonneg (by linarith)
  have hLL0 : 0 ≤ log (log N) := log_nonneg (by linarith)
  have hLL : log (log N) ≤ 0.112 * log N := task194_loglog_bound (log N) hL
  have hLX : log X ≤ 0.6 * log N := by
    have hh := log_le_log hX hXV
    rw [log_div hNp.ne' hV.ne', hlv] at hh
    linarith
  have hsum : log X + log (U N) ≤ log N := by
    have hh := log_le_log hX hXV
    rw [log_div hNp.ne' hV.ne', hlv] at hh
    linarith
  have hdiff : 0 ≤ log X - log (U N) := sub_nonneg.mpr (log_le_log hU hUX)
  have hsquared : (log X ^ 2 - log (U N) ^ 2) / 2 ≤ 0.5 * log N * log (X / U N) := by
    rw [log_div hX.ne' hU.ne']
    nlinarith [mul_le_mul_of_nonneg_right hsum hdiff]
  have huquad := task194_U_quadratic N hN
  have hroot : 3 * log N ≤ √(U N) := by
    apply (Real.le_sqrt (by positivity) hU.le).mpr
    nlinarith
  have hx2 : log X ^ 2 ≤ 0.36 * log N ^ 2 := by
    have hh := pow_le_pow_left₀ hLX0 hLX 2
    nlinarith
  have herr2 : log X ^ 2 / √(U N) ≤ 0.12 * log N := by
    apply (div_le_iff₀ (sqrt_pos.mpr hU)).mpr
    nlinarith
  have hratio : log X ^ 2 / U N ≤ 0.04 := by
    apply (div_le_iff₀ hU).mpr
    nlinarith
  let K : ℕ := ⌊log X / log 2⌋₊
  have hlog2 : 0.693 < log (2 : ℝ) := by linarith [Real.log_two_gt_d9]
  have hK1 : 1 ≤ K := by
    apply Nat.le_floor
    apply (le_div_iff₀ (by linarith : 0 < log (2 : ℝ))).mpr
    have hh := log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ X by linarith)
    simpa using hh
  have hKR : (K : ℝ) ≤ log N := by
    have hh : (K : ℝ) ≤ log X / log 2 := Nat.floor_le (by positivity)
    have hh' := (div_le_iff₀ (by linarith : 0 < log (2 : ℝ))).mpr
      (show log X ≤ log N * log 2 by nlinarith)
    exact hh.trans hh'
  have hH : (∑ k ∈ Icc 2 K, (1 : ℝ) / k) ≤ log (log N) := by
    have hh := harmonic_le_one_add_log K
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
    have hset : Icc 1 K = insert 1 (Icc 2 K) := by ext k; simp; omega
    rw [hset, sum_insert (by simp)] at hh
    norm_num only [Nat.cast_one, inv_one] at hh
    have hlogK : log (K : ℝ) ≤ log (log N) := log_le_log (by exact_mod_cast (show 0 < K by omega)) hKR
    simp only [one_div]
    linarith
  have hH0 : 0 ≤ ∑ k ∈ Icc 2 K, (1 : ℝ) / k := by positivity
  have herr3 : 2 * (log X ^ 2 / U N * ∑ k ∈ Icc 2 K, (1 : ℝ) / k) ≤ 0.00896 * log N := by
    have hh := mul_le_mul hratio (hH.trans hLL) hH0 (by norm_num : (0 : ℝ) ≤ 0.04)
    nlinarith
  unfold amEnergyEnvelope
  apply mul_le_mul_of_nonneg_left _ hX.le
  change (log X ^ 2 - log (U N) ^ 2) / 2 + 0.105 * log X + log X ^ 2 / √(U N) +
      2 * (log X ^ 2 / U N * ∑ k ∈ Icc 2 K, (1 : ℝ) / k) ≤ _
  linarith

/-- Full real parameter bookkeeping for the retained dyadic argument
in displays 6.10 and 6.19 on pages 170 and 173. -/
theorem task194_bracket (N : ℝ) (hN : exp 30.95 ≤ N) (M : ℝ) (hVM : V N ≤ M)
    (hMU : M ≤ N / U N) (q : ℕ) (hq : 2 ≤ q) :
    ((((⌊(N : ℝ) / M⌋₊ - ⌊U N⌋₊) / q : ℕ) : ℝ) + 1) * (5 * (M + 1 / 2) + q * Real.log q) ≤
      5 * N / q + 5 * M + N / M * Real.log q + q * Real.log q := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ Real.log N := (le_log_iff_exp_le hNp).mpr hN
  obtain ⟨_, hU, hV, hlu, hlv⟩ := task194_logs N hNp hL
  obtain ⟨hU15, hV13, hUV, hNVU⟩ := task194_full_params N hN
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hUV' : U N ≤ V N := by
    apply (Real.log_le_log_iff hU hV).mp
    rw [hlu, hlv]
    linarith
  have hM0 : 0 < M := hV.trans_le hVM
  have hUM : U N ≤ M := hUV'.trans hVM
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0.5 ≤ Real.log q := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hq2
    linarith [Real.log_two_gt_d9]
  have hUA : U N ≤ N / M := by
    rw [le_div_iff₀ hM0]
    rw [le_div_iff₀ hU] at hMU
    nlinarith
  have hA : (N : ℝ) / M ≤ M * U N := by
    have hh : (N : ℝ) / M ≤ N / V N := div_le_div_of_nonneg_left hNp.le hV hVM
    nlinarith [mul_le_mul_of_nonneg_right hUM hU.le]
  have hfloor : (⌊(N : ℝ) / M⌋₊ - ⌊U N⌋₊ : ℕ) ≤ ⌊(N : ℝ) / M⌋₊ := Nat.sub_le _ _
  have hsub : ((⌊(N : ℝ) / M⌋₊ - ⌊U N⌋₊ : ℕ) : ℝ) ≤ N / M - U N + 1 := by
    rw [Nat.cast_sub (Nat.floor_mono hUA)]
    have ht := Nat.lt_floor_add_one (U N)
    have ha := Nat.floor_le (div_nonneg hNp.le hM0.le)
    linarith
  have hdiv : (((⌊(N : ℝ) / M⌋₊ - ⌊U N⌋₊) / q : ℕ) : ℝ) ≤
      (N / M - U N + 1) / q := by
    have ht : (((⌊(N : ℝ) / M⌋₊ - ⌊U N⌋₊) / q : ℕ) : ℝ) ≤
        ((⌊(N : ℝ) / M⌋₊ - ⌊U N⌋₊ : ℕ) : ℝ) / q := by
      exact Nat.cast_div_le
    exact ht.trans (div_le_div_of_nonneg_right hsub hq0.le)
  calc
    _ ≤ ((N / M - U N + 1) / q + 1) * (5 * (M + 1 / 2) + q * Real.log q) := by
      gcongr
    _ ≤ _ := by
      have hneg : 0 ≤ (U N - 1) * Real.log q - 2.5 := by
        nlinarith [mul_nonneg (show 0 ≤ U N - 6 by linarith) (show 0 ≤ Real.log q - 0.5 by linarith)]
      have hm := mul_nonneg hM0.le (show 0 ≤ 2.5 * U N - 5 by linarith)
      have hn : 0 ≤ 5 * M * (U N - 1) - 2.5 * (N / M) + 2.5 * (U N - 1) := by
        nlinarith
      have hid : (5 * N / q + 5 * M + N / M * Real.log q + q * Real.log q) -
          (((N / M - U N + 1) / q + 1) * (5 * (M + 1 / 2) + q * Real.log q)) =
          (5 * M * (U N - 1) - 2.5 * (N / M) + 2.5 * (U N - 1)) / q +
            ((U N - 1) * Real.log q - 2.5) := by
        field_simp
        ring
      apply sub_nonneg.mp
      rw [hid]
      exact add_nonneg (div_nonneg hn hq0.le) hneg

/-- Full real parameter bookkeeping for the retained dyadic argument
in displays 6.10 and 6.19 on pages 170 and 173. -/
theorem task194_floor_UV (N : ℝ) (hN : exp 30.95 ≤ N) : U N * V N ≤ (⌊N⌋₊ : ℝ) := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  obtain ⟨_, hU, hV, hlu, hlv⟩ := task194_logs N hNp hL
  have hLL0 : 0 ≤ log (log N) := log_nonneg (by linarith)
  have hhalf : U N * V N ≤ N / 2 := by
    apply (Real.log_le_log_iff (mul_pos hU hV) (by positivity : 0 < N / 2)).mp
    rw [Real.log_mul hU.ne' hV.ne', Real.log_div hNp.ne' (by norm_num), hlu, hlv]
    linarith [Real.log_two_lt_d9]
  have hN2 : 2 ≤ N := by
    have hlarge : (15000 : ℝ) ≤ N := Constants.exp9634_ge.trans
      ((Real.exp_le_exp.mpr (by norm_num : (9.634 : ℝ) ≤ 30.95)).trans hN)
    linarith
  have hf := Nat.lt_floor_add_one N
  exact hhalf.trans (by linarith)

open Finset in
/-- A uniform square root budget for the retained dyadic profile.
The numerical coefficients are internal bounds for displays 6.10 and 6.22
on pages 170 and 174. -/
theorem task194_affine_budget (J : ℕ) (L T h : ℝ) (hJ : 1 ≤ J) (hL : 30.95 ≤ L)
    (hhlo : 0.693 ≤ h) (hhhi : h ≤ 0.694) (hT : T ≤ 0.2672 * L)
    (hlast : ((J : ℝ) - 1) * h ≤ T) (hnext : T ≤ (J : ℝ) * h + 0.001) :
    (∑ j ∈ range J, √(0.5 * L * (T + 0.384 - j * h))) ≤ 0.1172 * L ^ 2 := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hLp : 0 < L := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hT0 : 0 ≤ T := (mul_nonneg (by linarith : (0 : ℝ) ≤ (J : ℝ) - 1) hh0).trans hlast
  have hbound : (J : ℝ) ≤ 0.4179 * L := by
    have hm := mul_le_mul_of_nonneg_left hhlo (show (0 : ℝ) ≤ (J : ℝ) - 1 by linarith)
    nlinarith
  have havg : T + 0.384 - h * ((J : ℝ) - 1) / 2 ≤ 0.15724 * L := by nlinarith
  have havg0 : 0 ≤ T + 0.384 - h * ((J : ℝ) - 1) / 2 := by nlinarith
  have hn (j : ℕ) (hj : j ∈ range J) :
      0 ≤ 0.5 * L * (T + 0.384) - (j : ℝ) * (0.5 * L * h) := by
    have hjr : (j : ℝ) ≤ (J : ℝ) - 1 := by
      have := mem_range.mp hj
      have : j + 1 ≤ J := by omega
      have hc : (j : ℝ) + 1 ≤ J := by exact_mod_cast this
      linarith
    have hm := mul_le_mul_of_nonneg_right hjr hh0
    have ht : 0 ≤ T + 0.384 - (j : ℝ) * h := by linarith
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 0.5 * L by positivity) ht]
  have hs := task194_affine_roots J (0.5 * L * (T + 0.384)) (0.5 * L * h) hn
  have heq (j : ℕ) : 0.5 * L * (T + 0.384) - (j : ℝ) * (0.5 * L * h) =
      0.5 * L * (T + 0.384 - (j : ℝ) * h) := by ring
  simp_rw [heq] at hs
  have hJ2 := pow_le_pow_left₀ (Nat.cast_nonneg J : (0 : ℝ) ≤ J) hbound 2
  have hm := mul_le_mul hJ2
    (mul_le_mul_of_nonneg_left havg (show (0 : ℝ) ≤ 0.5 * L by positivity))
    (mul_nonneg (show (0 : ℝ) ≤ 0.5 * L by positivity) havg0) (sq_nonneg (0.4179 * L))
  have he : (J : ℝ) * ((J : ℝ) * (0.5 * L * (T + 0.384)) -
      (0.5 * L * h) * ((J : ℝ) * (J - 1)) / 2) =
      (J : ℝ) ^ 2 * (0.5 * L * (T + 0.384 - h * ((J : ℝ) - 1) / 2)) := by ring
  rw [he] at hs
  have hc : (0.4179 * L) ^ 2 * (0.5 * L * (0.15724 * L)) ≤ (0.1172 * L ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (L ^ 2)]
  have hsq := hs.trans (hm.trans hc)
  have hp : 0 ≤ ∑ j ∈ range J, √(0.5 * L * (T + 0.384 - j * h)) := by positivity
  nlinarith [sq_nonneg (0.1172 * L ^ 2)]

open U1543 Finset in
/-- The retained affine dyadic bound derived from displays 6.10 to 6.22
on pages 170 to 174, with the correct block endpoints. -/
noncomputable def fourthAffineBound (N : ℝ) (q : ℕ) : ℝ :=
  √(0.6111 * N) * ∑ j ∈ range (Jn ⌊N⌋₊ (U N) (V N)),
    √(0.5 * log N * (log (N / (U N * V N)) + 0.384 - j * log 2)) *
      (√(5 * N / q) + √5 * √(2 ^ j * V N) +
        √(N * log q) / √(2 ^ j * V N) + √(q * log q))
open U1543 Finset in
/-- The pure logarithmic dyadic bound is bounded by its affine profile
and the four elementary square root kernels from page 173. -/
theorem task194_fourth_affine (N : ℝ) (q : ℕ) (hN : exp 30.95 ≤ N) (hq : 2 ≤ q) :
    fourthLogBound ⌊N⌋₊ (U N) (V N) q ≤ fourthAffineBound N q := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hLp : 0 < log N := by linarith
  obtain ⟨_, hU, hV, hlu, hlv⟩ := task194_logs N hNp hL
  have hUVfloor := task194_floor_UV N hN
  have hjlast := (J_props ⌊N⌋₊ (U N) (V N) hU hV hUVfloor).1
  have hfloorN := Nat.floor_le hNp.le
  have hlq : 0 ≤ log (q : ℝ) := log_natCast_nonneg q
  unfold fourthLogBound fourthAffineBound
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  let M : ℝ := 2 ^ j * V N
  let X : ℝ := (⌊N⌋₊ : ℝ) / M
  let T : ℝ := log (N / (U N * V N))
  let w : ℝ := 0.5 * log N * (T + 0.384 - j * log 2)
  let G : ℝ := ((((⌊X⌋₊ - ⌊U N⌋₊) / q : ℕ) : ℝ) + 1) *
    (5 * (M + 1 / 2) + q * log q)
  let Br : ℝ := 5 * N / q + 5 * M + N / M * log q + q * log q
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hVM : V N ≤ M := by dsimp [M]; nlinarith
  have hM : 0 < M := hV.trans_le hVM
  have hMUfloor : M ≤ (⌊N⌋₊ : ℝ) / U N := by
    apply le_trans _ hjlast
    dsimp [M]
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply pow_le_pow_right₀ (by norm_num)
    have := mem_range.mp hj
    omega
  have hUX : U N ≤ X := by
    apply (le_div_iff₀ hM).mpr
    have hh := (le_div_iff₀ hU).mp hMUfloor
    nlinarith
  have hX : 0 < X := hU.trans_le hUX
  have hXN : X ≤ N / M := div_le_div_of_nonneg_right hfloorN hM.le
  have hXV : X ≤ N / V N := hXN.trans (div_le_div_of_nonneg_left hNp.le hV hVM)
  have hMU : M ≤ N / U N := hMUfloor.trans (div_le_div_of_nonneg_right hfloorN hU.le)
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hBr0 : 0 ≤ Br := by dsimp [Br]; positivity
  have hcount : (⌊X⌋₊ - ⌊U N⌋₊) / q ≤ (⌊N / M⌋₊ - ⌊U N⌋₊) / q :=
    Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.floor_mono hXN) _)
  have hG : G ≤ Br := by
    have hh := task194_bracket N hN M hVM hMU q hq
    apply le_trans _ hh
    dsimp [G]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.add_le_add_right hcount 1
  have hlogX : log (X / U N) ≤ T - j * log 2 := by
    have hh := log_le_log (div_pos hX hU) (div_le_div_of_nonneg_right hXN hU.le)
    have he : log ((N / M) / U N) = T - j * log 2 := by
      dsimp [T, M]
      rw [log_div (div_pos hNp (by positivity)).ne' hU.ne',
        log_div hNp.ne' (by positivity), log_mul (by positivity) hV.ne', log_pow,
        log_div hNp.ne' (mul_pos hU hV).ne', log_mul hU.ne' hV.ne']
      ring
    rwa [he] at hh
  have hlogX0 : 0 ≤ log (X / U N) := log_nonneg ((le_div_iff₀ hU).mpr (by simpa using hUX))
  have hw0 : 0 ≤ w := by
    dsimp [w]
    apply mul_nonneg (by positivity)
    linarith
  have hd : amEnergyEnvelope (U N) X ≤ X * w := by
    apply (task194_density_profile N X hN hUX hXV).trans
    apply mul_le_mul_of_nonneg_left _ hX.le
    dsimp [w]
    nlinarith [mul_le_mul_of_nonneg_left hlogX (show (0 : ℝ) ≤ 0.5 * log N by positivity)]
  have hen : G * amEnergyEnvelope (U N) X ≤ (N / M) * Br * w := by
    calc
      _ ≤ G * (X * w) := mul_le_mul_of_nonneg_left hd hG0
      _ = (G * X) * w := by ring
      _ ≤ (Br * (N / M)) * w :=
        mul_le_mul_of_nonneg_right (mul_le_mul hG hXN hX.le hBr0) hw0
      _ = _ := by ring
  have hsplit : √Br ≤ √(5 * N / q) + √5 * √M + √(N * log q) / √M + √(q * log q) := by
    have hh := sqrt_add4_le (5 * N / q) (5 * M) (N / M * log q) (q * log q)
      (by positivity) (by positivity) (by positivity) (by positivity)
    have he1 : √(5 * M) = √5 * √M := Real.sqrt_mul (by norm_num) M
    have he2 : √(N / M * log q) = √(N * log q) / √M := by
      rw [show N / M * log q = N * log q / M by ring, Real.sqrt_div' _ hM.le]
    rwa [he1, he2] at hh
  change √(0.6111 * M) * √(G * amEnergyEnvelope (U N) X) ≤
    √(0.6111 * N) * (√w * (√(5 * N / q) + √5 * √M + √(N * log q) / √M + √(q * log q)))
  calc
    _ ≤ √(0.6111 * M) * √((N / M) * Br * w) :=
      mul_le_mul_of_nonneg_left (sqrt_le_sqrt hen) (sqrt_nonneg _)
    _ = √(0.6111 * N) * √w * √Br := by
      rw [← Real.sqrt_mul (by positivity)]
      have he : (0.6111 * M) * ((N / M) * Br * w) = (0.6111 * N) * w * Br := by field_simp
      rw [he, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsplit (mul_nonneg (sqrt_nonneg (0.6111 * N)) (sqrt_nonneg w))]

open U1543 Finset in
/-- The actual floor endpoint window and its retained root budget
for display 6.10 on page 170 and the sum in display 6.22 on page 174. -/
lemma task194_J_window (N : ℝ) (hN : exp 30.95 ≤ N) :
    ((Jn ⌊N⌋₊ (U N) (V N) : ℝ) - 1) * log 2 ≤ log (N / (U N * V N)) ∧
      log (N / (U N * V N)) ≤ (Jn ⌊N⌋₊ (U N) (V N) : ℝ) * log 2 + 0.001 := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  obtain ⟨_, hU, hV, hlu, hlv⟩ := task194_logs N hNp hL
  have huvp := mul_pos hU hV
  have huv := task194_floor_UV N hN
  have hfloor : (⌊N⌋₊ : ℝ) ≤ N := Nat.floor_le hNp.le
  have hNlarge : (15000 : ℝ) ≤ N := Constants.exp9634_ge.trans
    ((exp_le_exp.mpr (by norm_num : (9.634 : ℝ) ≤ 30.95)).trans hN)
  have hnlarge : 15000 ≤ ⌊N⌋₊ := Nat.le_floor hNlarge
  have hnr : (15000 : ℝ) ≤ ⌊N⌋₊ := by exact_mod_cast hnlarge
  have hnpos : (0 : ℝ) < ⌊N⌋₊ := by linarith
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hF0 : 0 ≤ log ((⌊N⌋₊ : ℝ) / (U N * V N)) / log 2 := by
    apply div_nonneg _ hl2.le
    exact log_nonneg ((le_div_iff₀ huvp).mpr (by simpa using huv))
  have hlo := Nat.floor_le hF0
  have hhi := Nat.lt_floor_add_one (log ((⌊N⌋₊ : ℝ) / (U N * V N)) / log 2)
  have hlast : ((Jn ⌊N⌋₊ (U N) (V N) : ℝ) - 1) * log 2 ≤
      log ((⌊N⌋₊ : ℝ) / (U N * V N)) := by
    apply (le_div_iff₀ hl2).mp
    simpa only [Jn, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hlo
  have hnext : log ((⌊N⌋₊ : ℝ) / (U N * V N)) <
      (Jn ⌊N⌋₊ (U N) (V N) : ℝ) * log 2 := by
    apply (div_lt_iff₀ hl2).mp
    simpa only [Jn, Nat.cast_add, Nat.cast_one] using hhi
  have hTf : log ((⌊N⌋₊ : ℝ) / (U N * V N)) ≤ log (N / (U N * V N)) :=
    log_le_log (div_pos hnpos huvp) (div_le_div_of_nonneg_right hfloor huvp.le)
  have hratio : N / (⌊N⌋₊ : ℝ) ≤ 1.001 := by
    apply (div_le_iff₀ hnpos).mpr
    have hh := Nat.lt_floor_add_one N
    nlinarith
  have hdiff : log N - log (⌊N⌋₊ : ℝ) ≤ 0.001 := by
    rw [← log_div hNp.ne' hnpos.ne']
    have hh := log_le_log (div_pos hNp hnpos) hratio
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.001)]
  have he : log (N / (U N * V N)) - log ((⌊N⌋₊ : ℝ) / (U N * V N)) =
      log N - log (⌊N⌋₊ : ℝ) := by
    rw [log_div hNp.ne' huvp.ne', log_div hnpos.ne' huvp.ne']
    ring
  exact ⟨hlast.trans hTf, by linarith⟩

open U1543 Finset in
/-- The actual floor endpoint window and its retained root budget
for display 6.10 on page 170 and the sum in display 6.22 on page 174. -/
theorem task194_actual_root_budget (N : ℝ) (hN : exp 30.95 ≤ N) :
    (∑ j ∈ range (Jn ⌊N⌋₊ (U N) (V N)),
      √(0.5 * log N * (log (N / (U N * V N)) + 0.384 - j * log 2))) ≤
        0.1172 * log N ^ 2 := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  obtain ⟨_, hU, hV, hlu, hlv⟩ := task194_logs N hNp hL
  have hJ : 1 ≤ Jn ⌊N⌋₊ (U N) (V N) := by unfold Jn; omega
  have hT : log (N / (U N * V N)) ≤ 0.2672 * log N := by
    rw [log_div hNp.ne' (mul_pos hU hV).ne', log_mul hU.ne' hV.ne', hlu, hlv]
    linarith [task194_loglog_bound (log N) hL]
  have hw := task194_J_window N hN
  exact task194_affine_budget _ _ _ _ hJ hL (by linarith [Real.log_two_gt_d9])
    (by linarith [Real.log_two_lt_d9]) hT hw.1 hw.2

open U1543 Finset in
/-- The first coefficient contribution of the retained affine fourth sum bound,
corresponding to the first term of display 6.22 on page 174. -/
theorem task194_first_affine_term (N : ℝ) (q : ℕ) (hN : exp 30.95 ≤ N) (hq : 1 ≤ q) :
    √(0.6111 * N) * √(5 * N / q) *
      (∑ j ∈ range (Jn ⌊N⌋₊ (U N) (V N)),
        √(0.5 * log N * (log (N / (U N * V N)) + 0.384 - j * log 2))) ≤
          0.2264 * A N q := by
  let S : ℝ := ∑ j ∈ range (Jn ⌊N⌋₊ (U N) (V N)),
    √(0.5 * log N * (log (N / (U N * V N)) + 0.384 - j * log 2))
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hSb : S ≤ 0.1172 * log N ^ 2 := task194_actual_root_budget N hN
  have hb : √(0.6111 * N) * √(5 * N / q) * S ≤ 0.2264 * N / √q * log N ^ 2 := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hc : √(0.6111 : ℝ) ≤ 0.8 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    have h5 : √(5 : ℝ) ≤ 2.25 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 0.6111), Real.sqrt_div' _ hq0.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
    calc
      _ ≤ (0.8 * √N) * (2.25 * √N / √q) * (0.1172 * log N ^ 2) := by gcongr
      _ = 0.21096 * N / √q * log N ^ 2 := by
        ring_nf
        rw [Real.sq_sqrt hNp.le]
        ring
      _ ≤ _ := by gcongr; norm_num
  apply hb.trans_eq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqhalf : (q : ℝ) ^ (1 / 2 : ℝ) = √q := (Real.sqrt_eq_rpow (q : ℝ)).symm
  unfold A
  rw [Real.rpow_neg hq0.le, hqhalf]
  ring

/-- LEAF. Remaining affine coefficient estimate for Lemma 6.7, pages 170 to 174.
This is a derived sufficient bound for display 6.22 on page 174 with retained
block endpoints. The first contribution is proved by task194_first_affine_term.
The two weighted middle terms and the q log q term remain to be bounded. -/
theorem task194_affine_numeric (N : ℝ) (q : ℕ)
    (hN : exp 30.95 ≤ N) (hq : 1 ≤ q)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    fourthAffineBound N q ≤
      0.2264 * A N q + 2.787 * B N + 0.0785 * C N q := by
  sorry

/-- LEAF. Remaining elementary envelope estimate for Lemma 6.7, pages 170 to 174.
This is a derived sufficient target for the constants in display 6.22 on page 174.
The dyadic endpoints of display 6.10 are retained. The prime energies have already
been removed by displays 6.13 to 6.17 on pages 171 and 172.
No uniform ratio claim from page 173 is assumed. -/
theorem task194_fourth_numeric (N : ℝ) (q : ℕ)
    (hN : exp 30.95 ≤ N) (hq : 1 ≤ q)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    fourthLogBound ⌊N⌋₊ (U N) (V N) q ≤
      0.2264 * A N q + 2.787 * B N + 0.0785 * C N q := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have hLp : 0 < log N := by linarith
  obtain ⟨hq1, hq2⟩ := task194_range_of_scales N q hNp hq hA hC hLp
  have hq15 := (task194_q_range N hNp hL q hq1 hq2).1
  exact (task194_fourth_affine N q hN (by omega)).trans
    (task194_affine_numeric N q hN hq hA hC)

/-- LEAF. Lemma 6.7, pages 170 to 174, in the nontrivial regime of page 168.
External inputs: Wang and Chen 1994 Lemma 2 and Rosser and Schoenfeld 1962.
The inclusive cutoff of display 3.8 is retained. -/
theorem fourth_sum (N c : ℝ) (a : ℤ) (q : ℕ) (θ : ℝ)
    (hN : exp 30.95 ≤ N) (hc : 0 < c) (hc1 : c < 1)
    (hq : 1 ≤ q) (hcop : a.natAbs.Coprime q) (hθ : |θ| ≤ 1)
    (hA : 0.28 * A N q < 1.0012 * N) (hC : 0.09 * C N q < 1.0012 * N) :
    ‖S4 N c ((a : ℝ) / q + θ / (q : ℝ) ^ 2)‖ ≤
      0.2264 * A N q + 2.787 * B N + 0.0785 * C N q := by
  let α : ℝ := (a : ℝ) / q + θ / (q : ℝ) ^ 2
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hN1 : 1 ≤ N := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 30.95)).trans hN
  have hU : 0 < U N := (exp_pos _).trans_le (Decomp109b.U_lower N hN)
  have hD : U1543.Dioph α a q := by
    refine ⟨hq, ?_, ?_⟩
    · simpa [Int.gcd_def, Nat.Coprime] using hcop
    · dsimp [α]
      simp only [add_sub_cancel_left, abs_div, abs_pow, Nat.abs_cast]
      exact div_le_div_of_nonneg_right hθ (by positivity)
  exact (task194_fourth_energy U1543.wc_lemma2 N c (U N) (V N) α a q hN1 hc hU
    (task194_V_lower N hN) hD).trans
      ((task194_fourth_envelope U1543.rs2_mertens N q hN).trans
        (task194_fourth_numeric N q hN hq hA hC))

/-- A joint arithmetic instance of all four sealed leaf hypotheses
in displays 6.1, 6.3 and 6.5 on page 168. -/
theorem task194_nontrivial_instance : exp 30.95 ≤ exp 100 ∧
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧ 1 ≤ (10000000000 : ℕ) ∧
    (1 : ℤ).natAbs.Coprime 10000000000 ∧ |(0 : ℝ)| ≤ 1 ∧
    0.28 * A (exp 100) 10000000000 < 1.0012 * exp 100 ∧
    0.09 * C (exp 100) 10000000000 < 1.0012 * exp 100 := by
  have hNp : 0 < exp (100 : ℝ) := exp_pos _
  have hqhalf : (10000000000 : ℝ) ^ (1 / 2 : ℝ) = 100000 := by
    calc
      _ = √(10000000000 : ℝ) := (Real.sqrt_eq_rpow _).symm
      _ = _ := by norm_num
  have hNhalf : (exp (100 : ℝ)) ^ (1 / 2 : ℝ) = exp 50 := by
    rw [Real.rpow_def_of_pos hNp, Real.log_exp]
    norm_num
  have hLpow : (100 : ℝ) ^ (2.5 : ℝ) = 100000 := by
    have hh : ((100 : ℝ) ^ (2.5 : ℝ)) ^ 2 = 100 ^ 5 := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)]
      norm_num
    have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 100) (2.5 : ℝ)
    nlinarith
  have he1 : (2 : ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_d9]
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he1 50
  have he50 : exp (50 : ℝ) = exp 1 ^ 50 := by simpa using Real.exp_nat_mul (1 : ℝ) 50
  rw [← he50] at he
  have he100 : exp (100 : ℝ) = exp 50 ^ 2 := by
    convert Real.exp_nat_mul (50 : ℝ) 2 using 1; norm_num
  refine ⟨Real.exp_le_exp.mpr (by norm_num), by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, ?_⟩
  · unfold A
    rw [Real.log_exp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10000000000), hqhalf]
    nlinarith
  · unfold C
    rw [hNhalf, hqhalf, Real.log_exp, hLpow, he100]
    norm_num at he ⊢
    nlinarith [exp_pos (50 : ℝ)]

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

#print axioms LeanLab.LiuWang2002.Decomp109.task194_crude_error
#print axioms LeanLab.LiuWang2002.Decomp109.task194_lcm_certificate
#print axioms LeanLab.LiuWang2002.Decomp109.task194_psi_crude
#print axioms LeanLab.LiuWang2002.Decomp109.crude

#print axioms LeanLab.LiuWang2002.Decomp109.task194_sum_transfer

#print axioms LeanLab.LiuWang2002.Decomp109.task194_coefficients

#print axioms LeanLab.LiuWang2002.Decomp109.task194_logs

#print axioms LeanLab.LiuWang2002.Decomp109.task194_q_range

#print axioms LeanLab.LiuWang2002.Decomp109.task194_q_log_upper

#print axioms LeanLab.LiuWang2002.Decomp109.task194_n65c

#print axioms LeanLab.LiuWang2002.Decomp109.task194_n66c

#print axioms LeanLab.LiuWang2002.Decomp109.task194_n65a

#print axioms LeanLab.LiuWang2002.Decomp109.task194_n65b

#print axioms LeanLab.LiuWang2002.Decomp109.task194_n66a

#print axioms LeanLab.LiuWang2002.Decomp109.task194_n66b

#print axioms LeanLab.LiuWang2002.Decomp109.task194_S2_le

#print axioms LeanLab.LiuWang2002.Decomp109.task194_S3_le

#print axioms LeanLab.LiuWang2002.Decomp109.task194_range_of_scales

#print axioms LeanLab.LiuWang2002.Decomp109.task194_second_of_wc
#print axioms LeanLab.LiuWang2002.Decomp109.second_sum

#print axioms LeanLab.LiuWang2002.Decomp109.task194_third_of_wc
#print axioms LeanLab.LiuWang2002.Decomp109.third_sum

#print axioms LeanLab.LiuWang2002.Decomp109.task194_V_lower

#print axioms LeanLab.LiuWang2002.Decomp109.fourthEnergyBound
#print axioms LeanLab.LiuWang2002.Decomp109.task194_fourth_energy

#print axioms LeanLab.LiuWang2002.Decomp109.task194_full_params

#print axioms LeanLab.LiuWang2002.Decomp109.amEnergyEnvelope
#print axioms LeanLab.LiuWang2002.Decomp109.task194_am_energy

#print axioms LeanLab.LiuWang2002.Decomp109.fourthLogBound
#print axioms LeanLab.LiuWang2002.Decomp109.task194_fourth_envelope

#print axioms LeanLab.LiuWang2002.Decomp109.task194_fourth_numeric
#print axioms LeanLab.LiuWang2002.Decomp109.fourth_sum

#print axioms LeanLab.LiuWang2002.Decomp109.task194_nontrivial_instance

#print axioms LeanLab.LiuWang2002.Decomp109.task194_affine_roots

#print axioms LeanLab.LiuWang2002.Decomp109.task194_weighted_roots

#print axioms LeanLab.LiuWang2002.Decomp109.task194_loglog_bound

#print axioms LeanLab.LiuWang2002.Decomp109.task194_U_quadratic

#print axioms LeanLab.LiuWang2002.Decomp109.task194_density_profile

#print axioms LeanLab.LiuWang2002.Decomp109.task194_bracket

#print axioms LeanLab.LiuWang2002.Decomp109.task194_floor_UV

#print axioms LeanLab.LiuWang2002.Decomp109.task194_affine_budget

#print axioms LeanLab.LiuWang2002.Decomp109.fourthAffineBound
#print axioms LeanLab.LiuWang2002.Decomp109.task194_fourth_affine

#print axioms LeanLab.LiuWang2002.Decomp109.task194_J_window

#print axioms LeanLab.LiuWang2002.Decomp109.task194_actual_root_budget

#print axioms LeanLab.LiuWang2002.Decomp109.task194_first_affine_term

#print axioms LeanLab.LiuWang2002.Decomp109.task194_affine_numeric
