/- AI wrote this Lean code for CODEX task406. Goldbach is open.
Robin Theorem 11, pp. 380 and 381, behind journal Lemma 4 p. 1216.
https://doi.org/10.4064/aa-42-4-367-389 -/
import LeanLab.BS2022GRH.RobinFinite406
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import LeanLab.JohnstonStarichkova.Theorem14

namespace LeanLab.BS2022GRH.Decomp406c
open Real Finset Classical
noncomputable section

/-- LEAF. Robin p. 380 proof of Theorem 11, reduction to primorials.
Between consecutive primorials omega n is at most k, and log log x over log x
decreases for x at least sixteen. Three prime factors force n at least thirty.
This is a comparison with a primorial, not the numerical upper bound. -/
theorem primorial_comparison (n : ℕ) (hn : 3 ≤ n) (hk : 3 ≤ n.primeFactors.card) :
    (n.primeFactors.card : ℝ) * log (log n) / log n ≤
      (n.primeFactors.card : ℝ) * log (log (primeProduct n.primeFactors.card)) /
        log (primeProduct n.primeFactors.card) := by
  have hpred : LeanLab.JohnstonStarichkova.Pge 0 = Nat.Prime := by
    funext p
    simp [LeanLab.JohnstonStarichkova.Pge]
  have hp := LeanLab.JohnstonStarichkova.prod_nth_le_ge 0 n.primeFactors
    (fun p hp => ⟨(Nat.mem_primeFactors.mp hp).1, Nat.zero_le p⟩)
  rw [hpred] at hp
  have hmin : primeProduct n.primeFactors.card ≤ n :=
    hp.trans (Nat.le_of_dvd (by omega : 0 < n) (Nat.prod_primeFactors_dvd n))
  have h30 : 30 ≤ primeProduct n.primeFactors.card := by
    have hprod : primeProduct 3 ≤ primeProduct n.primeFactors.card := by
      unfold primeProduct
      apply prod_le_prod_of_subset_of_one_le'
      · exact range_subset_range.mpr hk
      · intro i hi hni
        exact (Nat.prime_nth_prime i).one_lt.le
    norm_num [primeProduct, prod_range_succ] at hprod
    exact hprod
  have hminR : (primeProduct n.primeFactors.card : ℝ) ≤ n := by exact_mod_cast hmin
  have h30R : (30 : ℝ) ≤ primeProduct n.primeFactors.card := by exact_mod_cast h30
  have hpos : (0 : ℝ) < primeProduct n.primeFactors.card := by linarith
  have h16 : exp 1 ≤ log (16 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [Real.log_two_gt_d9, Real.exp_one_lt_d9]
  have hlogP : exp 1 ≤ log (primeProduct n.primeFactors.card) :=
    h16.trans (log_le_log (by norm_num) (by linarith))
  have hmono := log_div_self_antitoneOn hlogP
    (hlogP.trans (log_le_log hpos hminR)) (log_le_log hpos hminR)
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n.primeFactors.card : (0 : ℝ) ≤ n.primeFactors.card)

/-- LEAF. Robin p. 380, the ten finite primorial checks in Theorem 11.
The maximum is attained at k equal to nine and is less than 1.38402. -/
theorem finite_primorial_ratio (k : ℕ) (hk : 3 ≤ k) (hk12 : k ≤ 12) :
    (k : ℝ) * log (log (primeProduct k)) / log (primeProduct k) ≤ 1.38402 := by
  exact RobinFinite406.finite_ratio k hk hk12

/-! ### Primes are 1 or 5 mod 6 -/

private theorem prime_mod_six {m : ℕ} (hm : m.Prime) (h2 : m ≠ 2) (h3 : m ≠ 3) :
    m % 6 = 1 ∨ m % 6 = 5 := by
  have hodd : m % 2 = 1 := by
    rcases hm.eq_two_or_odd with h | h
    · exact absurd h h2
    · exact h
  have h3m : ¬ (3 ∣ m) := by
    intro hd
    rcases hm.eq_one_or_self_of_dvd 3 hd with h | h <;> omega
  have hmod3 : m % 3 ≠ 0 := fun h => h3m (Nat.dvd_of_mod_eq_zero h)
  have e2 : m % 6 % 2 = m % 2 := Nat.mod_mod_of_dvd m (by norm_num : 2 ∣ 6)
  have e3 : m % 6 % 3 = m % 3 := Nat.mod_mod_of_dvd m (by norm_num : 3 ∣ 6)
  have hlt : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  omega

/-! ### Counting primes below `X` -/

private theorem count_prime_le (X : ℕ) : Nat.count Nat.Prime X ≤ X / 3 + 4 := by
  classical
  set S : Finset ℕ := (range X).filter (fun m => m % 6 = 1 ∨ m % 6 = 5) with hSdef
  have hstep1 : Nat.count Nat.Prime X ≤ (insert 2 (insert 3 S)).card := by
    rw [Nat.count_eq_card_filter_range]
    apply card_le_card
    intro m hm
    simp only [mem_filter, mem_range] at hm
    obtain ⟨hmX, hmp⟩ := hm
    by_cases h2 : m = 2
    · simp [h2]
    by_cases h3 : m = 3
    · simp [h3]
    have h6 := prime_mod_six hmp h2 h3
    simp only [mem_insert, hSdef, mem_filter, mem_range]
    tauto
  have hstep2 : (insert 2 (insert 3 S)).card ≤ S.card + 2 := by
    have h1 := card_insert_le (2 : ℕ) (insert 3 S)
    have h2 := card_insert_le (3 : ℕ) S
    omega
  have hstep3 : S.card ≤ 2 * (X / 6 + 1) := by
    have hsub : S ⊆ (range (X / 6 + 1)).biUnion
        (fun j => ({6 * j + 1, 6 * j + 5} : Finset ℕ)) := by
      intro m hm
      simp only [hSdef, mem_filter, mem_range] at hm
      obtain ⟨hmX, hm6⟩ := hm
      have hdiv : m = 6 * (m / 6) + m % 6 := (Nat.div_add_mod m 6).symm
      refine mem_biUnion.mpr ⟨m / 6, ?_, ?_⟩
      · simp only [mem_range]
        have hle : m / 6 ≤ X / 6 := Nat.div_le_div_right (by omega)
        omega
      · have hdm := Nat.div_add_mod m 6
        rcases hm6 with h | h
        · simp only [mem_insert, mem_singleton]
          left; omega
        · simp only [mem_insert, mem_singleton]
          right; omega
    calc S.card ≤ ((range (X / 6 + 1)).biUnion
          (fun j => ({6 * j + 1, 6 * j + 5} : Finset ℕ))).card := card_le_card hsub
      _ ≤ ∑ j ∈ range (X / 6 + 1), ({6 * j + 1, 6 * j + 5} : Finset ℕ).card :=
            card_biUnion_le
      _ ≤ ∑ _j ∈ range (X / 6 + 1), 2 := by
            apply sum_le_sum
            intro j _
            have h := card_insert_le (6 * j + 1) ({6 * j + 5} : Finset ℕ)
            simp only [card_singleton] at h
            omega
      _ = 2 * (X / 6 + 1) := by simp [mul_comm]
  have hstep4 : 2 * (X / 6) ≤ X / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    calc 2 * (X / 6) * 3 = 6 * (X / 6) := by ring
      _ ≤ X := by rw [mul_comm]; exact Nat.div_mul_le_self X 6
  omega

/-! ### The finite range -/

private theorem count_finite :
    ∀ k ∈ Finset.Ico 13 63, Nat.count Nat.Prime ((11 * (k + 1) + 3) / 4) ≤ k := by
  decide +kernel

/-! ### Lower bound for the k-th prime -/

private theorem ceil_four : ∀ n : ℕ, 11 * n ≤ 4 * ((11 * n + 3) / 4) := by
  intro n
  have h := Nat.div_add_mod (11 * n + 3) 4
  have hlt := Nat.mod_lt (11 * n + 3) (by norm_num : 0 < 4)
  omega

private theorem nth_prime_ge (k : ℕ) (hk : 13 ≤ k) :
    11 * (k + 1) ≤ 4 * Nat.nth Nat.Prime k := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hceil := ceil_four (k + 1)
  by_cases hsmall : k < 63
  · have hmem : k ∈ Finset.Ico 13 63 := by
      simp only [mem_Ico]; omega
    have hcount := count_finite k hmem
    have hle : (11 * (k + 1) + 3) / 4 ≤ Nat.nth Nat.Prime k :=
      (Nat.count_le_iff_le_nth hinf).mp hcount
    omega
  · have hbig : 63 ≤ k := by omega
    set M := (11 * (k + 1) + 3) / 4 with hMdef
    have hMc : Nat.count Nat.Prime M ≤ M / 3 + 4 := count_prime_le M
    have hMle : 4 * M ≤ 11 * (k + 1) + 3 := by
      rw [hMdef, mul_comm 4]
      exact Nat.div_mul_le_self (11 * (k + 1) + 3) 4
    -- M ≤ (11k+14)/4
    have hM2 : M ≤ (11 * k + 14) / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
      omega
    have hM3 : M / 3 ≤ (11 * k + 14) / 12 := by
      calc M / 3 ≤ ((11 * k + 14) / 4) / 3 := Nat.div_le_div_right hM2
        _ = (11 * k + 14) / 12 := by rw [Nat.div_div_eq_div_mul]
    have hM4 : M / 3 + 4 ≤ k := by
      have hmul : 12 * (M / 3 + 4) ≤ 12 * k := by
        have h1 : 12 * (M / 3) ≤ 12 * ((11 * k + 14) / 12) := by
          exact Nat.mul_le_mul_left 12 hM3
        have h2 : 12 * ((11 * k + 14) / 12) ≤ 11 * k + 14 := by
          rw [mul_comm]; exact Nat.div_mul_le_self (11 * k + 14) 12
        omega
      exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
    have hcount2 : Nat.count Nat.Prime M ≤ k := le_trans hMc hM4
    have hle : M ≤ Nat.nth Nat.Prime k := (Nat.count_le_iff_le_nth hinf).mp hcount2
    omega

/-! ### The geometric step -/

private theorem geometric (k : ℕ) (hk : 0 < k) :
    ((k : ℝ) + 1) ^ k ≤ (11 / 4) * (k : ℝ) ^ k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlog : log (1 + 1 / (k : ℝ)) ≤ 1 / (k : ℝ) := by
    have h := log_le_sub_one_of_pos (x := 1 + 1 / (k : ℝ)) (by positivity)
    have h1 : 1 + 1 / (k : ℝ) - 1 = 1 / (k : ℝ) := by ring
    linarith
  have hbase : ((k : ℝ) + 1) / (k : ℝ) = 1 + 1 / (k : ℝ) := by
    field_simp
  have hdiv : ((k : ℝ) + 1) ^ k / (k : ℝ) ^ k = (((k : ℝ) + 1) / (k : ℝ)) ^ k :=
    (div_pow _ _ _).symm
  have hkp : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hk0 k
  have hexp : (((k : ℝ) + 1) / (k : ℝ)) ^ k ≤ 11 / 4 := by
    have hlog2 : log ((((k : ℝ) + 1) / (k : ℝ)) ^ k) ≤ 1 := by
      rw [log_pow, hbase]
      have hkk : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
      have hm := mul_le_mul_of_nonneg_left hlog hk0.le
      linarith [hm, hkk]
    have hpos : (0 : ℝ) < ((k : ℝ) + 1) / (k : ℝ) := by positivity
    calc (((k : ℝ) + 1) / (k : ℝ)) ^ k = exp (log ((((k : ℝ) + 1) / (k : ℝ)) ^ k)) := by
          rw [exp_log (pow_pos hpos k)]
      _ ≤ exp 1 := exp_le_exp.mpr hlog2
      _ ≤ 11 / 4 := by linarith [exp_one_lt_d9]
  rw [← hdiv] at hexp
  rw [div_le_iff₀ hkp] at hexp
  linarith [hexp]

/-! ### Base case at 13 -/

private theorem primeProduct_13 : primeProduct 13 = 304250263527210 := by
  have h5 : Nat.nth Nat.Prime 5 = 13 := by
    have hc : Nat.count Nat.Prime 13 = 5 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 13)
  have h6 : Nat.nth Nat.Prime 6 = 17 := by
    have hc : Nat.count Nat.Prime 17 = 6 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 17)
  have h7 : Nat.nth Nat.Prime 7 = 19 := by
    have hc : Nat.count Nat.Prime 19 = 7 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 19)
  have h8 : Nat.nth Nat.Prime 8 = 23 := by
    have hc : Nat.count Nat.Prime 23 = 8 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 23)
  have h9 : Nat.nth Nat.Prime 9 = 29 := by
    have hc : Nat.count Nat.Prime 29 = 9 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 29)
  have h10 : Nat.nth Nat.Prime 10 = 31 := by
    have hc : Nat.count Nat.Prime 31 = 10 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 31)
  have h11 : Nat.nth Nat.Prime 11 = 37 := by
    have hc : Nat.count Nat.Prime 37 = 11 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 37)
  have h12 : Nat.nth Nat.Prime 12 = 41 := by
    have hc : Nat.count Nat.Prime 41 = 12 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 41)
  norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11, h12,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]

/-- The product of the first `k` primes is positive. -/
private theorem primeProduct_pos (k : ℕ) : 0 < primeProduct k := by
  unfold primeProduct
  exact prod_pos (fun i _ => (Nat.prime_nth_prime i).pos)

private theorem primeProduct_succ (k : ℕ) :
    primeProduct (k + 1) = primeProduct k * Nat.nth Nat.Prime k := by
  unfold primeProduct
  rw [prod_range_succ]

/-! ### `k^k ≤ N_k` -/

private theorem nat_pow_le_primeProduct (k : ℕ) (hk : 13 ≤ k) :
    (k : ℝ) ^ k ≤ (primeProduct k : ℝ) := by
  induction k, hk using Nat.le_induction with
  | base =>
      have hle : (13 : ℕ) ^ 13 ≤ primeProduct 13 := by
        rw [primeProduct_13]; norm_num
      have hle' : (13 : ℝ) ^ 13 ≤ (primeProduct 13 : ℝ) := by exact_mod_cast hle
      simpa using hle'
  | succ k hk ih =>
      have hN := primeProduct_succ k
      have hp : (11 : ℝ) * (k + 1) ≤ 4 * (Nat.nth Nat.Prime k : ℝ) := by
        have h := nth_prime_ge k hk
        exact_mod_cast h
      have hp' : (11 / 4) * ((k : ℝ) + 1) ≤ (Nat.nth Nat.Prime k : ℝ) := by
        nlinarith [hp]
      have hk0 : 0 < k := by omega
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
      have hg := geometric k hk0
      have hpnn : (0 : ℝ) ≤ (Nat.nth Nat.Prime k : ℝ) := by positivity
      have hNk : (0 : ℝ) ≤ (primeProduct k : ℝ) := by positivity
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, pow_succ]
      calc ((k : ℝ) + 1) ^ k * ((k : ℝ) + 1)
          ≤ ((11 / 4) * (k : ℝ) ^ k) * ((k : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hg (by positivity)
        _ = (k : ℝ) ^ k * ((11 / 4) * ((k : ℝ) + 1)) := by ring
        _ ≤ (primeProduct k : ℝ) * (Nat.nth Nat.Prime k : ℝ) :=
            mul_le_mul ih hp' (by positivity) hNk
        _ = ((primeProduct (k + 1) : ℕ) : ℝ) := by rw [hN]; push_cast; ring

/-- LEAF. Robin p. 372 Theorem 4 display 15, used on p. 381 for k at least thirteen.
The logarithm of N_k equals theta at the kth prime. This is a lower bound
for that logarithm and has no omega ratio or 1.3841 conclusion. -/
theorem primorial_log_lower (k : ℕ) (hk : 13 ≤ k) :
    (k : ℝ) * log k ≤ log (primeProduct k) := by

  have hk13 : (13 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hkey := nat_pow_le_primeProduct k hk
  have hpp : (0 : ℝ) < (primeProduct k : ℝ) := by
    have h := primeProduct_pos k
    exact_mod_cast h
  calc (k : ℝ) * log k = log ((k : ℝ) ^ k) := (log_pow _ _).symm
    _ ≤ log (primeProduct k) := log_le_log (pow_pos hk0 k) hkey

/-- The universal scalar maximum used on Robin p. 381 is below 0.37. -/
theorem log_le_point37_mul (t : ℝ) (ht : 0 < t) : log t ≤ 0.37 * t := by
  have h := log_le_sub_one_of_pos (div_pos ht (exp_pos 1))
  rw [log_div ht.ne' (exp_pos 1).ne', log_exp] at h
  have he : (1 : ℝ) / exp 1 ≤ 0.37 := by
    apply (div_le_iff₀ (exp_pos 1)).mpr
    nlinarith [exp_one_gt_d9]
  have hm := mul_le_mul_of_nonneg_right he ht.le
  calc
    log t ≤ t / exp 1 := by linarith
    _ ≤ 0.37 * t := by simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hm

/-- At least thirteen primes give the simpler 1.37 ratio, Robin p. 381.
CONDITIONAL ON primorial_log_lower. -/
theorem tail_primorial_ratio (k : ℕ) (hk : 13 ≤ k) :
    (k : ℝ) * log (log (primeProduct k)) / log (primeProduct k) ≤ 1.37 := by
  have hkR : (13 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog : 1 ≤ log (k : ℝ) := by
    rw [le_log_iff_exp_le hk0]
    linarith [exp_one_lt_d9]
  have ha : exp 1 ≤ (k : ℝ) * log k := by nlinarith [exp_one_lt_d9]
  have hb := primorial_log_lower k hk
  have hmono := log_div_self_antitoneOn ha (ha.trans hb) hb
  have hapos : 0 < (k : ℝ) * log k := by positivity
  have hlp : 0 < log (primeProduct k) := hapos.trans_le hb
  have hmul := mul_le_mul_of_nonneg_left hmono hk0.le
  have heq : (k : ℝ) * (log ((k : ℝ) * log k) / ((k : ℝ) * log k)) =
      1 + log (log k) / log k := by
    rw [log_mul hk0.ne' (by positivity)]
    field_simp
  rw [heq] at hmul
  have hsmall : log (log (k : ℝ)) / log k ≤ 0.37 :=
    (div_le_iff₀ (by positivity : 0 < log (k : ℝ))).mpr
      (log_le_point37_mul _ (by positivity))
  calc
    _ = (k : ℝ) * (log (log (primeProduct k)) / log (primeProduct k)) := by ring
    _ ≤ 1 + log (log k) / log k := hmul
    _ ≤ 1.37 := by linarith

/-- Integers with at most two distinct prime factors satisfy the journal bound.
This is the small omega case in Robin Theorem 11, p. 380. -/
theorem small_omega (n : ℕ) (hn : 3 ≤ n) (hk : n.primeFactors.card ≤ 2) :
    (n.primeFactors.card : ℝ) < 1.3841 * log n / log (log n) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < log (n : ℝ) := by
    rw [lt_log_iff_exp_lt (by linarith : 0 < (n : ℝ))]
    linarith [exp_one_lt_d9]
  have hll : 0 < log (log (n : ℝ)) := log_pos hlog
  have hs := log_le_point37_mul (log n) (by linarith)
  have hkR : (n.primeFactors.card : ℝ) ≤ 2 := by exact_mod_cast hk
  apply (lt_div_iff₀ hll).mpr
  nlinarith [mul_le_mul_of_nonneg_right hkR hll.le]

/-- Exact statement of PublishedInputs232.lemma4_robin from Robin's three proof steps.
CONDITIONAL ON primorial_log_lower. The comparison and finite checks are proved. -/
theorem lemma4_robin : PaperInputs148.Lemma4J := by
  intro n hn
  by_cases hk : n.primeFactors.card ≤ 2
  · exact small_omega n hn hk
  have hk3 : 3 ≤ n.primeFactors.card := by omega
  have hcomp := primorial_comparison n hn hk3
  have hratio : (n.primeFactors.card : ℝ) * log (log n) / log n ≤ 1.38402 := by
    apply hcomp.trans
    by_cases hk12 : n.primeFactors.card ≤ 12
    · exact finite_primorial_ratio _ hk3 hk12
    · exact (tail_primorial_ratio _ (by omega)).trans (by norm_num)
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < log (n : ℝ) := by
    rw [lt_log_iff_exp_lt (by linarith : 0 < (n : ℝ))]
    linarith [exp_one_lt_d9]
  apply (lt_div_iff₀ (log_pos hlog)).mpr
  have hmul := (div_le_iff₀ (by linarith : 0 < log (n : ℝ))).mp hratio
  nlinarith

end
end LeanLab.BS2022GRH.Decomp406c

#print axioms LeanLab.BS2022GRH.Decomp406c.primorial_comparison
#print axioms LeanLab.BS2022GRH.Decomp406c.finite_primorial_ratio
#print axioms LeanLab.BS2022GRH.Decomp406c.primorial_log_lower
#print axioms LeanLab.BS2022GRH.Decomp406c.log_le_point37_mul
#print axioms LeanLab.BS2022GRH.Decomp406c.tail_primorial_ratio
#print axioms LeanLab.BS2022GRH.Decomp406c.small_omega
#print axioms LeanLab.BS2022GRH.Decomp406c.lemma4_robin
