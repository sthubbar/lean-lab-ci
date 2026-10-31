/-
AI-written Lean code, Claude, 2026-10-25, run 20261025T2003Z-426, unit U-1528, DECOMPOSE.
P0020 P. J. Campbell 2026, A Sharper Explicit Result for the Sum of Two Almost Primes,
arXiv 2608.09488 v1. The explicit prime estimates of Section 4 rest on Rosser-Schoenfeld 1962,
Illinois J. Math. 6, Theorems 5 to 7, p. 70. This file splits the elementary part of that
material, Mertens' first theorem with explicit constants, into leaves, following the
Rosser-Schoenfeld style elementary argument: log n! by Legendre's formula.

Already in Mathlib, not restated: `Chebyshev.theta_le_log4_mul_x` (θ x ≤ x log 4),
`Nat.factorization_factorial_le_div_pred` (v_p(n!) ≤ n/(p - 1)), `log_add_one_le_harmonic`,
`ArithmeticFunction.vonMangoldt_sum`, `Chebyshev.psi_le`.
Already in the lab, not restated: `AlmostPrimes.RSLogSum.sum_log_div_lt_log`
(Σ_{p ≤ n} log p/p < log n for n ≥ 1000), `PNTSieve.Mertens.C_ge`, `C_le` (constant 7),
`PNTSieve.Mertens.sum_log_div_pred_le` (Σ log p/(p(p - 1)) ≤ 6), `log_factorial_ge`.
The lab modules are not imported (none is built in this checkout); the one helper re-proved
here, `log_factorial_ge'`, is proved, not a leaf.

All 11 leaves are filled by OpenAI Codex task160, 2026-10-28. AI wrote the Lean proofs.
Build and axiom evidence: build/codex-task160.log. All statements are unchanged.
Assemblies:
`mertens1_upper_nat`, `mertens1_lower_nat`, `mertens1_abs` (|Σ_{p ≤ x} log p/p - log x| ≤ 2 for
x ≥ 1), `vonMangoldt_mertens_nat`.
Known mathematics. Goldbach is open.
-/
import Mathlib

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.AlmostPrimes.Decomp1528a

/-! ### Legendre's formula, the two halves -/

/-- LEAF. Legendre upper half: for every natural n,
log n! ≤ n Σ_{p ≤ n} log p / p + n Σ_{p ≤ n} log p / (p (p - 1)).
Proof: log n! = Σ_{p ≤ n} v_p(n!) log p and v_p(n!) ≤ n/(p - 1) = n/p + n/(p(p - 1)).
Rosser-Schoenfeld 1962, Section 3, p. 70 style; Ingham, The Distribution of Prime Numbers,
Thm 7. Unit U-1528. -/
theorem log_factorial_le_sum (n : ℕ) :
    log (n.factorial : ℝ) ≤
      (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p +
        (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hfac : log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * log p := by
    rw [Real.log_nat_eq_sum_factorization]
    apply Finsupp.sum_of_support_subset
    · intro p hp
      rw [Nat.support_factorization] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hle := (Nat.Prime.dvd_factorial hpp).1 (Nat.dvd_of_mem_primeFactors hp)
      rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc]
      exact ⟨⟨Nat.zero_le _, hle⟩, hpp⟩
    · intro p _; simp
  rw [hfac, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hb : (n.factorial.factorization p : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
    have hb : (n.factorial.factorization p : ℝ) ≤ (n / (p - 1) : ℕ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp n
    have hc : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      simpa only [Nat.cast_sub hpp.one_le, Nat.cast_one] using
        (Nat.cast_div_le (m := n) (n := p - 1) (α := ℝ))
    exact hb.trans hc
  calc (n.factorial.factorization p : ℝ) * log p ≤
      ((n : ℝ) / ((p : ℝ) - 1)) * log p :=
        mul_le_mul_of_nonneg_right hb (Real.log_nonneg hp1.le)
    _ = _ := by field_simp; ring

/-- LEAF. Legendre lower half: for every natural n,
n Σ_{p ≤ n} log p / p - θ(n) ≤ log n!.
Proof: v_p(n!) ≥ ⌊n/p⌋ ≥ n/p - 1, summed against log p. Ingham, Thm 7. Unit U-1528. -/
theorem sum_sub_theta_le_log_factorial (n : ℕ) :
    (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p - θ n ≤ log (n.factorial : ℝ) := by
  have hfac : log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * log p := by
    rw [Real.log_nat_eq_sum_factorization]
    apply Finsupp.sum_of_support_subset
    · intro p hp
      rw [Nat.support_factorization] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hle := (Nat.Prime.dvd_factorial hpp).1 (Nat.dvd_of_mem_primeFactors hp)
      rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc]
      exact ⟨⟨Nat.zero_le _, hle⟩, hpp⟩
    · intro p _; simp
  rw [hfac, theta_eq_sum_primesLE_log, mul_sum, ← sum_sub_distrib]
  apply sum_le_sum
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlog : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
  have hleg : n / p ≤ n.factorial.factorization p := by
    rw [Nat.factorization_factorial hpp (b := Nat.log p n + 2) (by omega)]
    simpa only [pow_one] using
      (Finset.single_le_sum (f := fun i : ℕ => n / p ^ i) (fun i _ => Nat.zero_le _)
        (show 1 ∈ Ico 1 (Nat.log p n + 2) by simp))
  have hfloor : (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hp0]
    have hlt : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by
      exact_mod_cast Nat.lt_div_mul_add (a := n) hpp.pos
    nlinarith
  have hcast : ((n / p : ℕ) : ℝ) ≤ (n.factorial.factorization p : ℝ) := by
    exact_mod_cast hleg
  calc (n : ℝ) * (log p / p) - log p = ((n : ℝ) / p - 1) * log p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hfloor.trans hcast) hlog

/-! ### The constant Σ_p log p/(p(p - 1)) = 0.75536... -/

set_option maxHeartbeats 800000 in
/-- LEAF. Head of the prime sum: Σ_{p ≤ 1000} log p / (p (p - 1)) ≤ 0.7545.
Python value 0.754375. Kernel check with rational bounds for log p. Rosser-Schoenfeld 1962,
(2.11) and p. 70, the constant E = -γ - Σ_p log p/(p(p - 1)). Unit U-1528. -/
theorem sum_log_div_pp1_head :
    ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.7545 := by
  let b : ℕ → ℕ := fun p => if p < 17 then 512 else 64
  let a : ℕ → ℕ := fun p => Nat.clog 2 (p ^ b p)
  let u : ℕ → ℚ := fun p =>
    if p = 2 then 0.6931471808 else
    if p = 3 then 1.0986122888 else
    if p = 5 then 1.6094379126 else (a p : ℚ) / b p * 0.6931471808
  have hlog (p : ℕ) (hp : p ∈ Nat.primesLE 1000) : log p ≤ (u p : ℝ) := by
    by_cases h2 : p = 2
    · subst p; simpa [u] using Real.log_two_lt_d9.le
    by_cases h3 : p = 3
    · subst p; simpa [u] using Real.log_three_lt_d9.le
    by_cases h5 : p = 5
    · subst p; simpa [u] using Real.log_five_lt_d9.le
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    have hpow : (p : ℝ) ^ b p ≤ (2 : ℝ) ^ a p := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (p ^ b p)
    have h := Real.log_le_log (pow_pos hp0 _) hpow
    rw [Real.log_pow, Real.log_pow] at h
    have hb : (0 : ℝ) < b p := by dsimp [b]; split_ifs <;> norm_num
    have hbound : log p ≤ (a p : ℝ) / b p * log 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hb]
      nlinarith only [h]
    calc log p ≤ (a p : ℝ) / b p * log 2 := hbound
      _ ≤ (a p : ℝ) / b p * 0.6931471808 :=
        mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by positivity)
      _ = (u p : ℝ) := by simp [u, h2, h3, h5]
  let cand : ℕ → Bool := fun p => decide (2 ≤ p) &&
    !(List.range' 2 30).any (fun d => decide (d < p) && p % d == 0)
  let C : Finset ℕ := (range 1001).filter (fun p => cand p = true)
  have hsub : Nat.primesLE 1000 ⊆ C := by
    intro p hp
    simp only [C, mem_filter, mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.le_of_mem_primesLE hp), ?_⟩
    have hpp := Nat.prime_of_mem_primesLE hp
    have hsmall : (List.range' 2 30).any (fun d => decide (d < p) && p % d == 0) = false := by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨d, hd, hdp⟩ := List.any_eq_true.mp h
      rw [List.mem_range'_1] at hd
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hdp
      have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hdp.2
      rcases (Nat.dvd_prime hpp).mp hdvd with h | h <;> omega
    simp [cand, hpp.two_le, hsmall]
  let v : ℕ → ℕ := fun p =>
    ⌈u p / ((p : ℚ) * ((p : ℚ) - 1)) * (10 : ℚ) ^ 10⌉₊
  have hcert : ∑ p ∈ C, v p ≤ 7545000000 := by
    dsimp only [C, cand, v, u, a, b]
    decide +kernel
  have hcertPrime : ∑ p ∈ Nat.primesLE 1000, v p ≤ 7545000000 :=
    (sum_le_sum_of_subset hsub).trans hcert
  have hv (p : ℕ) : (u p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ (v p : ℝ) / 10 ^ 10 := by
    have h : u p / ((p : ℚ) * ((p : ℚ) - 1)) * (10 : ℚ) ^ 10 ≤ (v p : ℚ) :=
      Nat.le_ceil _
    have hr : (u p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) * (10 : ℝ) ^ 10 ≤ (v p : ℝ) := by
      exact_mod_cast h
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 10)).2 hr
  calc ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ Nat.primesLE 1000, (u p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        apply sum_le_sum
        intro p hp
        apply div_le_div_of_nonneg_right (hlog p hp)
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
        exact mul_nonneg (Nat.cast_nonneg p) (by linarith)
    _ ≤ ∑ p ∈ Nat.primesLE 1000, (v p : ℝ) / 10 ^ 10 := sum_le_sum (fun p _ => hv p)
    _ = ((∑ p ∈ Nat.primesLE 1000, v p : ℕ) : ℝ) / 10 ^ 10 := by
      rw [← sum_div, Nat.cast_sum]
    _ ≤ (7545000000 : ℝ) / 10 ^ 10 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcertPrime
    _ = 0.7545 := by norm_num

/-- LEAF. Tail over all integers: for every n, Σ_{1000 < m ≤ n} log m / (m (m - 1)) ≤ 0.009.
Python value of the full tail 0.007908; g(1000) = 0.0089078. Proof: log m/(m(m - 1)) ≤ g(m - 1) - g(m) with
g(t) = (log t + 2)/t for t ≥ 1000, telescoping. Rosser-Schoenfeld 1962, p. 70 style. Unit U-1528. -/
theorem sum_log_div_pp1_tail (n : ℕ) :
    ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 0.009 := by
  let g : ℕ → ℝ := fun k => (log k + 2) / k
  have hstrong : ∀ k : ℕ, 1000 ≤ k →
      ∑ m ∈ Ioc 1000 k, log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ g 1000 - g k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [sum_Ioc_succ_top hk]
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hk0 : (0 : ℝ) < k := by linarith
      have hl := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < k + 1) hk0)
      rw [Real.log_div (by positivity : (k : ℝ) + 1 ≠ 0) hk0.ne'] at hl
      have he : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
      rw [he] at hl
      have hb : ((k : ℝ) + 1) * (log ((k : ℝ) + 1) - log k) ≤ 2 := by
        calc ((k : ℝ) + 1) * (log ((k : ℝ) + 1) - log k) ≤
            ((k : ℝ) + 1) * (1 / k) := mul_le_mul_of_nonneg_left hl (by positivity)
          _ ≤ 2 := by rw [mul_one_div, div_le_iff₀ hk0]; linarith
      have heq : g k - g (k + 1) -
          log (k + 1 : ℕ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1)) =
          (2 - ((k : ℝ) + 1) * (log ((k : ℝ) + 1) - log k)) /
            ((k : ℝ) * ((k : ℝ) + 1)) := by
        dsimp [g]
        push_cast
        simp only [add_sub_cancel_right]
        field_simp
        ring
      have hstep := div_nonneg (sub_nonneg.mpr hb)
        (show 0 ≤ (k : ℝ) * ((k : ℝ) + 1) by positivity)
      rw [← heq] at hstep
      linarith
  by_cases hn : 1000 ≤ n
  · have h := hstrong n hn
    have hgn : 0 ≤ g n := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact div_nonneg (by linarith [Real.log_nonneg hn1]) (Nat.cast_nonneg n)
    have hlog : log (1000 : ℝ) < 7 := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1000)
        (by norm_num : (1000 : ℝ) ≤ 2 ^ 10)
      rw [Real.log_pow] at h
      norm_num only [Nat.cast_ofNat] at h
      linarith [Real.log_two_lt_d9]
    have hg : g 1000 ≤ 0.009 := by dsimp [g]; norm_num; linarith
    linarith
  · rw [Ioc_eq_empty (by omega), sum_empty]
    norm_num

/-- LEAF. Prime tail inside the integer tail: for every n,
Σ_{p ≤ n} log p/(p(p - 1)) ≤ Σ_{p ≤ 1000} log p/(p(p - 1)) + Σ_{1000 < m ≤ n} log m/(m(m - 1)),
because every term is nonnegative. Unit U-1528. -/
theorem sum_log_div_pp1_split (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) +
        ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
  let f : ℕ → ℝ := fun p => log p / ((p : ℝ) * ((p : ℝ) - 1))
  have hnon (p : ℕ) : 0 ≤ f p := by
    rcases p with _ | p
    · simp [f]
    have hp : (1 : ℝ) ≤ (p + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p)
    exact div_nonneg (Real.log_nonneg hp) (mul_nonneg (by positivity) (by linarith))
  have hsub : Nat.primesLE n ⊆ Nat.primesLE 1000 ∪ Ioc 1000 n := by
    intro p hp
    rcases le_or_gt p 1000 with h | h
    · exact mem_union_left _ (Nat.mem_primesLE.mpr ⟨h, Nat.prime_of_mem_primesLE hp⟩)
    · exact mem_union_right _ (mem_Ioc.mpr ⟨h, Nat.le_of_mem_primesLE hp⟩)
  calc ∑ p ∈ Nat.primesLE n, f p ≤ ∑ p ∈ Nat.primesLE 1000 ∪ Ioc 1000 n, f p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnon p)
    _ = ∑ p ∈ Nat.primesLE 1000, f p + ∑ p ∈ Ioc 1000 n, f p := by
      apply sum_union
      apply disjoint_left.mpr
      intro p hp hq
      have := Nat.le_of_mem_primesLE hp
      have := (mem_Ioc.mp hq).1
      omega

/-- Σ_{p ≤ n} log p / (p (p - 1)) ≤ 0.7635 for every n, from the three leaves above. -/
theorem sum_log_div_pp1_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.7635 := by
  have h1 := sum_log_div_pp1_split n
  have h2 := sum_log_div_pp1_head
  have h3 := sum_log_div_pp1_tail n
  linarith

/-! ### log n! against n log n -/

/-- `n log n - n ≤ log n!`, the same statement as the lab's `PNTSieve.Mertens.log_factorial_ge`,
re-proved here so this file imports only Mathlib. PROVED. -/
theorem log_factorial_ge' (n : ℕ) : (n : ℝ) * log n - n ≤ log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn : (0 : ℝ) < n := by exact_mod_cast h
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hb : (n : ℝ) ^ n / n.factorial ≤ exp n := by
    have := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn.le n
    simpa using this
  have hb' : (n : ℝ) ^ n ≤ exp n * n.factorial := by
    rwa [div_le_iff₀ hf] at hb
  have hl := Real.log_le_log (by positivity) hb'
  rw [Real.log_mul (exp_pos _).ne' hf.ne', Real.log_exp, Real.log_pow] at hl
  linarith

/-- `log n! ≤ n log n`, from `n! ≤ n^n`. PROVED. -/
theorem log_factorial_le (n : ℕ) : log (n.factorial : ℝ) ≤ (n : ℝ) * log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc log (n.factorial : ℝ) ≤ log ((n : ℝ) ^ n) := Real.log_le_log hf h1
    _ = (n : ℝ) * log n := by rw [Real.log_pow]

/-! ### Mertens' first theorem, explicit -/

/-- **Mertens' first theorem, upper half, explicit**: Σ_{p ≤ n} log p/p ≤ log n + log 4 for n ≥ 1.
Assembly from `sum_sub_theta_le_log_factorial`, `log_factorial_le` and Mathlib's
`theta_le_log4_mul_x`. -/
theorem mertens1_upper_nat (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, log p / p ≤ log n + log 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := sum_sub_theta_le_log_factorial n
  have h2 := log_factorial_le n
  have h3 := theta_le_log4_mul_x (x := (n : ℝ)) hn'.le
  have h4 : (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p ≤ (n : ℝ) * (log n + log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left h4 hn'

/-- **Mertens' first theorem, lower half, explicit**: log n - 1.7635 ≤ Σ_{p ≤ n} log p/p for
n ≥ 1. Assembly from `log_factorial_le_sum`, `sum_log_div_pp1_le`, `log_factorial_ge'`. -/
theorem mertens1_lower_nat (n : ℕ) (hn : 1 ≤ n) :
    log n - 1.7635 ≤ ∑ p ∈ Nat.primesLE n, log p / p := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := log_factorial_le_sum n
  have h2 := sum_log_div_pp1_le n
  have h3 := log_factorial_ge' n
  have h4 : (n : ℝ) * (log n - 1.7635) ≤ (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left h4 hn'

/-- LEAF. Small range of the real form: for 1 ≤ x < 5,
|Σ_{p ≤ ⌊x⌋} log p / p - log x| ≤ 2. The sums are 0, log 2/2, log 2/2 + log 3/3 and log x < log 5.
Python: worst value 0.897 near x = 5. Unit U-1528. -/
theorem mertens1_small {x : ℝ} (hx : 1 ≤ x) (hx5 : x < 5) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 2 := by
  have hx0 : 0 < x := by linarith
  have hn : ⌊x⌋₊ ≤ 4 := by
    have : ⌊x⌋₊ < 5 := (Nat.floor_lt hx0.le).2 hx5
    omega
  have hnon : 0 ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p := by
    apply sum_nonneg
    intro p _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hsum : ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p ≤ log 2 / 2 + log 3 / 3 := by
    have hsub := Nat.primesLE_mono hn
    have h := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => log p / p) hsub
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    have hset : Nat.primesLE 4 = {2, 3} := by decide
    simpa [hset] using h
  have hl : 0 ≤ log x := Real.log_nonneg hx
  have hu : log x ≤ log 5 := Real.log_le_log hx0 hx5.le
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have h5 := Real.log_five_lt_d9
  rw [abs_le]
  constructor <;> linarith

/-- LEAF. Floor step: for x ≥ 5, log x ≤ log ⌊x⌋ + 0.2, since x < ⌊x⌋ + 1 and
log(1 + 1/5) = 0.1823 < 0.2. Unit U-1528. -/
theorem log_le_log_floor_add {x : ℝ} (hx : 5 ≤ x) : log x ≤ log (⌊x⌋₊ : ℝ) + 0.2 := by
  have hn5 : 5 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hn0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hx0 hn0)
  rw [Real.log_div hx0.ne' hn0.ne'] at h
  have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn5' : (5 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn5
  have hb : x / (⌊x⌋₊ : ℝ) - 1 ≤ 0.2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hn0]
    nlinarith
  linarith

/-- **Mertens' first theorem, explicit, real form**: for every real x ≥ 1,
|Σ_{p ≤ x} log p / p - log x| ≤ 2. Assembly from the leaves of this file and Mathlib.
Python: the true deviation lies in [-1.3323, 0] up to 2·10^6, Rosser-Schoenfeld (3.21), (3.24). -/
theorem mertens1_abs {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 2 := by
  rcases lt_or_ge x 5 with h5 | h5
  · exact mertens1_small hx h5
  have hn1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hf0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hn1
  have hlog : log (⌊x⌋₊ : ℝ) ≤ log x := Real.log_le_log hf0 hfx
  have hU := mertens1_upper_nat ⌊x⌋₊ hn1
  have hL := mertens1_lower_nat ⌊x⌋₊ hn1
  have hS := log_le_log_floor_add h5
  have h4 : log (4 : ℝ) < 2 := by
    have he := Real.exp_one_gt_d9
    have h2 : exp (2 : ℝ) = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
    rw [Real.log_lt_iff_lt_exp (by norm_num), h2]; nlinarith
  rw [abs_le]; constructor <;> linarith

/-! ### The von Mangoldt form -/

/-- LEAF. Chebyshev's identity: for every natural n,
log n! = Σ_{1 ≤ m ≤ n} Λ(m) ⌊n/m⌋. Proof: log k = Σ_{m ∣ k} Λ(m) (Mathlib `vonMangoldt_sum`)
summed over k ≤ n, then swap. Ingham, Thm 7 proof; Montgomery-Vaughan, Multiplicative Number
Theory I, Section 2.2. Unit U-1528. -/
theorem log_factorial_eq_vonMangoldt (n : ℕ) :
    log (n.factorial : ℝ) =
      ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m * ((n / m : ℕ) : ℝ) := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt n
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at h
  rw [← Real.sum_log_eq_log_factorial]
  simpa only [ArithmeticFunction.log_apply, ← Finset.Icc_add_one_left_eq_Ioc, zero_add] using h

/-- LEAF. Upper half for Λ: for n ≥ 1, n Σ_{m ≤ n} Λ(m)/m ≤ log n! + ψ(n), from
n/m ≤ ⌊n/m⌋ + 1 and `log_factorial_eq_vonMangoldt`. Montgomery-Vaughan I, Section 2.2.
Unit U-1528. -/
theorem vonMangoldt_sum_le (n : ℕ) :
    (n : ℝ) * ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m ≤
      log (n.factorial : ℝ) + ψ n := by
  have hpsi : ψ (n : ℝ) = ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m := by
    simp [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc]
  rw [log_factorial_eq_vonMangoldt, hpsi, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro m hm
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hdiv : (n : ℝ) / m ≤ ((n / m : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hm0']
    have hlt : (n : ℝ) < ((n / m : ℕ) : ℝ) * m + m := by
      exact_mod_cast Nat.lt_div_mul_add (a := n) hm0
    nlinarith
  have hnon : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
  calc (n : ℝ) * (ArithmeticFunction.vonMangoldt m / m) =
        ArithmeticFunction.vonMangoldt m * ((n : ℝ) / m) := by ring
    _ ≤ ArithmeticFunction.vonMangoldt m * (((n / m : ℕ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hdiv hnon
    _ = _ := by ring

/-- LEAF. Lower half for Λ: for every n, log n! ≤ n Σ_{m ≤ n} Λ(m)/m, from ⌊n/m⌋ ≤ n/m and
`log_factorial_eq_vonMangoldt`. Montgomery-Vaughan I, Section 2.2. Unit U-1528. -/
theorem log_factorial_le_vonMangoldt_sum (n : ℕ) :
    log (n.factorial : ℝ) ≤ (n : ℝ) * ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m := by
  rw [log_factorial_eq_vonMangoldt, mul_sum]
  apply sum_le_sum
  intro m hm
  have hnon : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
  calc ArithmeticFunction.vonMangoldt m * ((n / m : ℕ) : ℝ) ≤
        ArithmeticFunction.vonMangoldt m * ((n : ℝ) / m) :=
      mul_le_mul_of_nonneg_left Nat.cast_div_le hnon
    _ = _ := by ring

/-- LEAF. Numeric step: for every real t ≥ 1, log 4 + 2 log t / √t ≤ 3; the maximum of
log t/√t is 2/e at t = e², and log 4 + 4/e = 2.858. Unit U-1528. -/
theorem log4_add_le_three {t : ℝ} (ht : 1 ≤ t) : log 4 + 2 * log t / √t ≤ 3 := by
  have ht0 : 0 < t := by linarith
  have hs : 0 < √t := Real.sqrt_pos.mpr ht0
  have h := Real.log_le_sub_one_of_pos (div_pos hs (Real.exp_pos 1))
  rw [Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_sqrt ht0.le] at h
  have hlog : log t ≤ 2 * √t / exp 1 := by
    calc log t = 2 * (log t / 2) := by ring
         _ ≤ 2 * (√t / exp 1) := mul_le_mul_of_nonneg_left (by linarith only [h]) (by norm_num)
         _ = _ := by ring
  have hdiv : 2 * log t / √t ≤ 4 / exp 1 := by
    calc 2 * log t / √t ≤ 2 * (2 * √t / exp 1) / √t :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by norm_num)) hs.le
         _ = _ := by field_simp; ring
  have h4 : log (4 : ℝ) < 1.4 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have he : (2.5 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hi : (4 : ℝ) / exp 1 ≤ 1.6 := by
    rw [div_le_iff₀ (exp_pos 1)]
    linarith
  linarith

/-- **Mertens' first theorem for Λ, explicit**: for n ≥ 1,
log n - 1 ≤ Σ_{m ≤ n} Λ(m)/m ≤ log n + 3. Python: the true deviation lies in [-0.627, 0] up to
2·10^5. Assembly from the leaves, `log_factorial_ge'`, `log_factorial_le` and Mathlib `psi_le`. -/
theorem vonMangoldt_mertens_nat (n : ℕ) (hn : 1 ≤ n) :
    log n - 1 ≤ ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m ∧
      ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m ≤ log n + 3 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set S := ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m with hSdef
  constructor
  · have h1 := log_factorial_le_vonMangoldt_sum n
    have h2 := log_factorial_ge' n
    have h4 : (n : ℝ) * (log n - 1) ≤ (n : ℝ) * S := by nlinarith
    exact le_of_mul_le_mul_left h4 hn'
  · have h1 := vonMangoldt_sum_le n
    have h2 := log_factorial_le n
    have h3 := psi_le hn1
    have h5 := log4_add_le_three hn1
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
    have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
    have h6 : 2 * √(n : ℝ) * log n = (n : ℝ) * (2 * log n / √(n : ℝ)) := by
      field_simp
      rw [Real.sq_sqrt hn'.le]; ring
    have h4 : (n : ℝ) * S ≤ (n : ℝ) * (log n + 3) := by
      have : (n : ℝ) * (log 4 + 2 * log n / √(n : ℝ)) ≤ (n : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left h5 hn'.le
      nlinarith
    exact le_of_mul_le_mul_left h4 hn'

/-! ### Vacuity instances -/

/-- The hypotheses of `mertens1_abs` hold at x = 7. -/
example : (1 : ℝ) ≤ 7 := by norm_num

/-- The hypotheses of `mertens1_small` hold at x = 2. -/
example : (1 : ℝ) ≤ 2 ∧ (2 : ℝ) < 5 := by norm_num

/-- `log_le_log_floor_add` at x = 5: its hypothesis holds. -/
example : (5 : ℝ) ≤ 5 := le_rfl

end LeanLab.AlmostPrimes.Decomp1528a
