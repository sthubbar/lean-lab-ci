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

/-- LEAF. Robin p. 372 Theorem 4 display 15, used on p. 381 for k at least thirteen.
The logarithm of N_k equals theta at the kth prime. This is a lower bound
for that logarithm and has no omega ratio or 1.3841 conclusion. -/
theorem primorial_log_lower (k : ℕ) (hk : 13 ≤ k) :
    (k : ℝ) * log k ≤ log (primeProduct k) := by
  sorry

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
