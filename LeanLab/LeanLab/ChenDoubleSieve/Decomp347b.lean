import LeanLab.ChenDoubleSieve.Decomp315a

/-!
The forced second prime in Upsilon 10 of Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, pages 35 to 37.
These finite identities preserve the sealed count and expose its exact difference
from a count that exempts both forced primes.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxRecDepth 20000
set_option exponentiation.threshold 1000
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task347
open Task275 Task315
open Wu41 (S)

/-- A forced prime below a real sifting level makes the literal count zero.
Source: page 35 Upsilon 10, derived modulus check. -/
theorem forced_prime_zero (A : Finset ℕ) (e D q : ℕ) (y : ℝ)
    (hq : q.Prime) (hqy : (q : ℝ) < y) (hqD : ¬ q ∣ D) (hqe : q ∣ e) :
    S A e D y = 0 := by
  unfold S
  rw [card_eq_zero, filter_eq_empty_iff]
  intro a _ ha
  exact ha.2 q hq hqy hqD (hqe.trans ha.1)

/-- Exempting the second forced prime changes exactly the terms below its level.
Source: page 36 expansion of S3 before equation 9.6, derived exact identity. -/
theorem forced_pair_split (A : Finset ℕ) (N p q : ℕ) (y : ℝ)
    (hq : q.Prime) (hqc : q.Coprime (N * p)) :
    S A (p * q) (N * p * q) y = S A (p * q) (N * p) y +
      if (q : ℝ) < y then S A (p * q) (N * p * q) y else 0 := by
  by_cases hqy : (q : ℝ) < y
  · rw [if_pos hqy, forced_prime_zero A (p * q) (N * p) q y hq hqy
      ((hq.coprime_iff_not_dvd).mp hqc) (dvd_mul_left q p), zero_add]
  · rw [if_neg hqy, add_zero]
    exact sieve_modulus_prime A (p * q) (N * p) q hq y (le_of_not_gt hqy)

/-- Buchstab expansion after exempting both forced primes.
Source: page 36 S3 expansion. The extra modulus factor is kept explicit. -/
theorem forced_pair_buchstab (A : Finset ℕ) (N p q : ℕ) (hq : q.Prime)
    {y : ℝ} (hqy : (q : ℝ) ≤ y) :
    S A (p * q) (N * p) q = S A (p * q) (N * p * q) y +
      ∑ r ∈ Wu41.PS (N * p * q) q y,
        S A (p * q * r) (N * p * q) r := by
  rw [← sieve_modulus_prime A (p * q) (N * p) q hq q le_rfl]
  apply buchstab_divisor A (p * q) (N * p * q) hqy
  intro r hr
  obtain ⟨hrp, _, _, hrc⟩ := Wu41.mem_PS.mp hr
  apply (hrp.coprime_iff_not_dvd).mpr
  intro hd
  apply ((hrp.coprime_iff_not_dvd).mp hrc)
  have hmul : p * q ∣ N * p * q := by
    refine ⟨N, ?_⟩
    ring
  exact hd.trans hmul

/-- The exact pair domain of the sealed Upsilon 10 coordinate.
Source: page 35 definition of Upsilon 10. -/
def crossingPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa2 ≤ p ∧
    (p : ℝ) < (N : ℝ) ^ sigma2 ∧ (N : ℝ) ^ sigma2 ≤ q ∧
    (q : ℝ) < Real.sqrt ((N : ℝ) / p))

/-- Membership in the crossing domain without evaluating its ambient finite cube.
Source: page 35 Upsilon 10, derived domain characterization. -/
theorem mem_crossingPairs {N p q : ℕ} :
    (p, q) ∈ crossingPairs N ↔ p < N ∧ q < N ∧ p.Prime ∧ q.Prime ∧
      p.Coprime N ∧ q.Coprime N ∧ (N : ℝ) ^ kappa2 ≤ p ∧
      (p : ℝ) < (N : ℝ) ^ sigma2 ∧ (N : ℝ) ^ sigma2 ≤ q ∧
      (q : ℝ) < Real.sqrt ((N : ℝ) / p) := by
  simp only [crossingPairs, Wu08Sum.P2, mem_filter, mem_product, mem_range]
  tauto

/-- The Upsilon 10 count that exempts both forced primes.
Source: page 36 divisor-quotient reading of the S3 expansion. -/
def exemptUpsilon10 (N : ℕ) : ℝ :=
  (∑ q ∈ crossingPairs N,
    S (primeSequence N) (q.1 * q.2) (N * q.1 * q.2) ((N : ℝ) ^ sigma1) : ℕ)

/-- The terms lost by the sealed modulus below the second sifting level.
Source: pages 35 and 36 Upsilon 10 and the S3 expansion, derived difference. -/
def crossingDefect (N : ℕ) : ℝ :=
  (∑ q ∈ crossingPairs N,
    if (q.2 : ℝ) < (N : ℝ) ^ sigma1 then
      S (primeSequence N) (q.1 * q.2) (N * q.1 * q.2) ((N : ℝ) ^ sigma1)
    else 0 : ℕ)

/-- The missing contribution is a nonnegative finite count.
Source: page 36 S3 expansion, derived helper. -/
theorem crossingDefect_nonneg (N : ℕ) : 0 ≤ crossingDefect N := Nat.cast_nonneg _

/-- The two Upsilon 10 readings differ by exactly the crossing contribution.
Source: pages 35 and 36, derived finite identity for the written S3 expansion. -/
theorem exemptUpsilon10_eq (N : ℕ) :
    exemptUpsilon10 N = sieveTerms N 9 + crossingDefect N := by
  have hpoint : ∀ q ∈ crossingPairs N,
      S (primeSequence N) (q.1 * q.2) (N * q.1 * q.2) ((N : ℝ) ^ sigma1) =
        S (primeSequence N) (q.1 * q.2) (N * q.1) ((N : ℝ) ^ sigma1) +
        if (q.2 : ℝ) < (N : ℝ) ^ sigma1 then
          S (primeSequence N) (q.1 * q.2) (N * q.1 * q.2) ((N : ℝ) ^ sigma1)
        else 0 := by
    intro q hq
    simp only [crossingPairs, Wu08Sum.P2, mem_filter, mem_product] at hq
    obtain ⟨_, hp, hqprime, _, hqc, _, hpT, hTq, _⟩ := hq
    have hpq : q.1 < q.2 := by exact_mod_cast hpT.trans_le hTq
    have hqnp : ¬ q.2 ∣ N * q.1 :=
      Wu08.not_dvd_mul_of hqprime hp (Ne.symm hpq.ne)
        ((hqprime.coprime_iff_not_dvd).mp hqc)
    exact forced_pair_split _ N q.1 q.2 _ hqprime
      ((hqprime.coprime_iff_not_dvd).mpr hqnp)
  have hsum := sum_congr rfl hpoint
  rw [sum_add_distrib] at hsum
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hsum
  push_cast at hcast
  simpa [exemptUpsilon10, crossingDefect, sieveTerms, crossingPairs, Nat.cast_sum] using hcast

/-- The sealed Upsilon 10 never exceeds the count that exempts both forced primes.
Source: pages 35 and 36, derived comparison. -/
theorem literalUpsilon10_le (N : ℕ) : sieveTerms N 9 ≤ exemptUpsilon10 N := by
  rw [exemptUpsilon10_eq]
  exact le_add_of_nonneg_right (crossingDefect_nonneg N)

/-- A squarefree prime difference realizes the modulus obstruction.
Source: page 36 S3 expansion, concrete nonvacuity check. -/
theorem crossing_instance :
    903 ∈ Wu08.Achen 992 ∧ Squarefree 903 ∧
      S {903} 21 2976 9 = 0 ∧ S {903} 21 20832 9 = 1 := by
  have hs : Wu41.Sifted 20832 9 903 := by
    intro q hq hq9 hqD
    have hsmall : q < 9 := by exact_mod_cast hq9
    interval_cases q <;> norm_num at *
  refine ⟨?_, by decide +kernel, ?_, ?_⟩
  · apply mem_image.mpr
    refine ⟨89, ?_, by norm_num⟩
    norm_num [mem_filter, mem_range]
  · exact forced_prime_zero {903} 21 2976 7 9 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · unfold S
    have he : ({903} : Finset ℕ).filter (fun a => 21 ∣ a ∧ Wu41.Sifted 20832 9 a) = {903} := by
      apply filter_eq_self.mpr
      intro a ha
      have ha' := mem_singleton.mp ha
      subst a
      exact ⟨by norm_num, hs⟩
    rw [he, card_singleton]

/-- The real cutoff conditions of Upsilon 10 hold at the concrete witness.
Source: page 35 Upsilon 10 and page 42 printed parameter choice. -/
theorem crossing_cutoffs_instance :
    (992 : ℝ) ^ kappa2 < 3 ∧ 3 < (992 : ℝ) ^ sigma2 ∧
      (992 : ℝ) ^ sigma2 < 7 ∧ 7 < (992 : ℝ) ^ sigma1 ∧
      (992 : ℝ) ^ sigma1 < 10 := by
  have hK : ((992 : ℝ) ^ kappa2) ^ 250 = (992 : ℝ) ^ 29 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    convert Real.rpow_natCast (992 : ℝ) 29 using 1 <;> norm_num [kappa2]
  have hT : ((992 : ℝ) ^ sigma2) ^ 500 = (992 : ℝ) ^ 141 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    convert Real.rpow_natCast (992 : ℝ) 141 using 1 <;> norm_num [sigma2]
  have hS : ((992 : ℝ) ^ sigma1) ^ 125 = (992 : ℝ) ^ 41 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    convert Real.rpow_natCast (992 : ℝ) 41 using 1 <;> norm_num [sigma1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra hnot
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (le_of_not_gt hnot) 250
    rw [hK] at h
    norm_num at h
  · by_contra hnot
    have h := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) sigma2) (le_of_not_gt hnot) 500
    rw [hT] at h
    norm_num at h
  · by_contra hnot
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7) (le_of_not_gt hnot) 500
    rw [hT] at h
    norm_num at h
  · by_contra hnot
    have h := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) sigma1) (le_of_not_gt hnot) 125
    rw [hS] at h
    norm_num at h
  · by_contra hnot
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) (le_of_not_gt hnot) 125
    rw [hS] at h
    norm_num at h

/-- The crossing pair is present at the exact printed real cutoffs.
Source: page 35 Upsilon 10 and page 42 printed parameter choice. -/
theorem crossing_pair_instance : (3, 7) ∈ crossingPairs 992 := by
  apply mem_crossingPairs.mpr
  obtain ⟨hK, hTlo, hThi, _, _⟩ := crossing_cutoffs_instance
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, hK.le, hTlo, hThi.le, ?_⟩
  exact (pair_sqrt_iff 992 3 7 (by norm_num)).mpr (by norm_num)

/-- A single counted crossing element makes the missing contribution positive.
Source: page 36 S3 expansion, derived finite positivity helper. -/
theorem crossingDefect_pos_of (N p q a : ℕ) (hpq : (p, q) ∈ crossingPairs N)
    (hqy : (q : ℝ) < (N : ℝ) ^ sigma1) (ha : a ∈ primeSequence N)
    (hd : p * q ∣ a) (hs : Wu41.Sifted (N * p * q) ((N : ℝ) ^ sigma1) a) :
    0 < crossingDefect N := by
  have hpos : 0 < S (primeSequence N) (p * q) (N * p * q) ((N : ℝ) ^ sigma1) := by
    apply card_pos.mpr
    exact ⟨a, mem_filter.mpr ⟨ha, hd, hs⟩⟩
  have hle := single_le_sum (fun t (_ : t ∈ crossingPairs N) =>
    Nat.zero_le (if (t.2 : ℝ) < (N : ℝ) ^ sigma1 then
      S (primeSequence N) (t.1 * t.2) (N * t.1 * t.2) ((N : ℝ) ^ sigma1)
    else 0)) hpq
  rw [if_pos hqy] at hle
  exact Nat.cast_pos.mpr (hpos.trans_le hle)

/-- The omitted count is strictly positive for the actual prime sequence at 992.
Source: page 36 S3 expansion, exact nonvacuity of the correction. This does not
negate the eventual first_half statement. -/
theorem crossingDefect_pos_instance : 0 < crossingDefect 992 := by
  obtain ⟨_, _, _, hSlo, hShi⟩ := crossing_cutoffs_instance
  have hs : Wu41.Sifted 20832 ((992 : ℝ) ^ sigma1) 903 := by
    intro q hq hqy hqD
    have hsmall : q < 10 := by exact_mod_cast hqy.trans hShi
    interval_cases q <;> norm_num at *
  have hm : 903 ∈ primeSequence 992 := by
    rw [primeSequence_decomposition]
    exact mem_union_left _ crossing_instance.1
  exact crossingDefect_pos_of 992 3 7 903 crossing_pair_instance hSlo hm
    (by norm_num) hs

end LeanLab.ChenDoubleSieve.Task347
