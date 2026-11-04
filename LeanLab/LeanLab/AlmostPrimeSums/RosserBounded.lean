import LeanLab.AlmostPrimeSums.RosserDefect

/-!
AI wrote this Lean code for CODEX task258. Goldbach is open.
The bounded cutoff part of the fundamental lemma is elementary. The
constant here depends on the cutoff bound B. This removes that regime
from the remaining analytic leaves without claiming uniformity in B.
Derived from Heath Brown pp. 31 to 35 and the density condition HR p. 142.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real BoundingSieve

/-- A coarse defect moment bound follows from the density product and the
sum of positive divisor densities. This estimate has no level decay.
Derived finite bound for Heath Brown p. 35 and density source HR p. 142. -/
theorem rosser_defect_moment_le_coarse (s : BoundingSieve) (K D z : ℝ)
    (hK : 0 ≤ K) (hz : 2 ≤ z)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (hden : LinearDensity s K)
    (upper : Bool) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n) ≤
      2 ^ s.prodPrimes.primeFactors.card *
        (log (z + 1) / log 2 * (1 + K / log 2)) := by
  classical
  let V := ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)
  have hV : 0 < V := Finset.prod_pos fun p hp => sub_pos.mpr
    (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  have hfilter : s.prodPrimes.primeFactors.filter
      (fun p : ℕ => (2 : ℝ) ≤ p ∧ (p : ℝ) < z + 1) = s.prodPrimes.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact ⟨by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le, by linarith [hP p hp]⟩
  have hinv : V⁻¹ ≤ log (z + 1) / log 2 * (1 + K / log 2) := by
    have hh := hden 2 (z + 1) le_rfl (by linarith)
    simpa only [hfilter, Finset.prod_inv_distrib] using hh
  have hsum : (∑ d ∈ s.prodPrimes.divisors, s.nu d) ≤
      2 ^ s.prodPrimes.primeFactors.card := by
    rw [← s.nu_mult.prodPrimeFactors_one_add_of_squarefree s.prodPrimes_squarefree]
    calc
      _ ≤ ∏ _p ∈ s.prodPrimes.primeFactors, (2 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          linarith [s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
        · intro p hp
          linarith [s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
      _ = _ := by simp
  have herr : |s.mainSum (rosserWeight D upper) - V| ≤
      2 ^ s.prodPrimes.primeFactors.card := by
    exact (rosser_mainSum_error_le_tail s z D (by linarith) hP upper).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d hd _ => (s.nu_pos_of_dvd_prodPrimes (Nat.mem_divisors.mp hd).1).le)).trans hsum)
  have hid : (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n) =
      |s.mainSum (rosserWeight D upper) - V| * V⁻¹ := by
    rw [rosser_mainSum_error_eq]
    change _ = (V * _) * V⁻¹
    field_simp [hV.ne']
  rw [hid]
  exact mul_le_mul herr hinv (inv_nonneg.mpr hV.le) (by positivity)

/-- For each fixed cutoff bound B the full exponential defect moment
estimate holds, uniformly in the sieve, z at most B and every admissible D.
The constant depends on K and B. This removes the bounded cutoff regime
from the general fundamental lemma. Derived from Heath Brown pp. 34 to 35
and the density condition on HR p. 142. -/
theorem rosser_defect_moment_exp_bounded (K B : ℝ) (hK : 0 ≤ K) (hB : 2 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ B → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      ∀ upper : Bool,
        (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n) ≤
          C * exp (-(log D / log z)) := by
  classical
  let M : ℕ := ⌈B⌉₊
  let R : ℝ := log (B + 1) / log 2 * (1 + K / log 2)
  let C : ℝ := 2 ^ M * R * exp ((M : ℝ) + 2)
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hR : 0 < R := by
    dsimp [R]
    apply mul_pos (div_pos (log_pos (by linarith)) hlog2)
    have hh : 0 ≤ K / log 2 := div_nonneg hK hlog2.le
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro s z D hz hzB hD hP hden upper
  have hz0 : 0 ≤ z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hcard : s.prodPrimes.primeFactors.card ≤ M := by
    have hsub : s.prodPrimes.primeFactors ⊆ Finset.range M := by
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_ceil.mpr ((hP p hp).trans_le hzB))
    simpa using Finset.card_le_card hsub
  have hprod : (s.prodPrimes : ℝ) ≤ z ^ M := by
    calc
      _ = ∏ p ∈ s.prodPrimes.primeFactors, (p : ℝ) := by
        rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree]
      _ ≤ ∏ _p ∈ s.prodPrimes.primeFactors, z :=
        Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p) (fun p hp => (hP p hp).le)
      _ = z ^ s.prodPrimes.primeFactors.card := by simp
      _ ≤ z ^ M := pow_le_pow_right₀ hz1 hcard
  have hbound : (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n) ≤
      2 ^ M * R := by
    refine (rosser_defect_moment_le_coarse s K D z hK hz hP hden upper).trans ?_
    apply mul_le_mul
    · exact pow_le_pow_right₀ (by norm_num) hcard
    · exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (log_le_log (by linarith) (by linarith)) hlog2.le) (by positivity)
    · have hlog : 0 ≤ log (z + 1) := log_nonneg (by linarith)
      positivity
    · positivity
  by_cases hsmall : (s.prodPrimes : ℝ) * z ^ 2 < D
  · have he := rosser_mainSum_error_eq s D upper
    rw [rosser_mainSum_exact_of_prod_bound s D z hz0 hP hsmall upper,
      sub_self, abs_zero] at he
    have hV : (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≠ 0 :=
      (Finset.prod_pos fun p hp => sub_pos.mpr
        (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp))).ne'
    have hzero := (mul_eq_zero.mp he.symm).resolve_left hV
    rw [hzero]
    exact (mul_pos hC (exp_pos _)).le
  · have hDpow : D ≤ z ^ (M + 2) := by
      calc
        D ≤ (s.prodPrimes : ℝ) * z ^ 2 := le_of_not_gt hsmall
        _ ≤ z ^ M * z ^ 2 := mul_le_mul_of_nonneg_right hprod (sq_nonneg z)
        _ = z ^ (M + 2) := (pow_add _ _ _).symm
    have hDpos : 0 < D := (pow_pos (by linarith : 0 < z) 10).trans_le hD
    have hlog := log_le_log hDpos hDpow
    rw [log_pow] at hlog
    have hs : log D / log z ≤ (M : ℝ) + 2 := by
      apply (div_le_iff₀ hlz).mpr
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at hlog
      exact hlog
    have he : 1 ≤ exp ((M : ℝ) + 2) * exp (-(log D / log z)) := by
      rw [← exp_add]
      exact one_le_exp_iff.mpr (by linarith)
    calc
      _ ≤ 2 ^ M * R := hbound
      _ ≤ (2 ^ M * R) * (exp ((M : ℝ) + 2) * exp (-(log D / log z))) :=
        le_mul_of_one_le_right (by positivity) he
      _ = C * exp (-(log D / log z)) := by dsimp [C]; ring

/-- The full weight and exponential error conclusion holds for each fixed
bounded cutoff range and general nonnegative K. The constant depends on
K and B. This is a derived bounded cutoff case of IK Lemma 6.3 and Theorem 6.9,
using the finite Rosser construction on Heath Brown pp. 30 to 35. -/
theorem fundamental_lemma_bounded (K B : ℝ) (hK : 0 ≤ K) (hB : 2 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ B → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      ∃ lp lm : ℕ → ℝ,
        (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
        (∀ d, lp d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        (∀ d, lm d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        IsUpperMoebius lp ∧
        (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) ∧
        |s.mainSum lp - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ∧
        |s.mainSum lm - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  obtain ⟨C, hC, hmoment⟩ := rosser_defect_moment_exp_bounded K B hK hB
  refine ⟨C, hC, ?_⟩
  intro s z D hz hzB hD hP hden
  have hzD : z ≤ D := by
    calc
      z = z ^ 1 := by simp
      _ ≤ z ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ D := hD
  obtain ⟨lp, lm, hb, hp1, hm1, hsp, hsm, hu, hl, hmp, hmm⟩ :=
    rosser_fundamental_weights s z D hzD (by linarith) hP
  have hV : 0 ≤ ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_nonneg fun p hp =>
      (sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp))).le
  have he : ∀ upper : Bool,
      |s.mainSum (rosserWeight D upper) -
        (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p))| ≤
        C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
    intro upper
    rw [rosser_mainSum_error_eq]
    exact (mul_le_mul_of_nonneg_left (hmoment s z D hz hzB hD hP hden upper) hV).trans_eq (by ring)
  refine ⟨lp, lm, hb, hp1, hm1, hsp, hsm, hu, hl, ?_, ?_⟩
  · simpa only [hmp] using he true
  · simpa only [hmm] using he false

end LeanLab.AlmostPrimeSums.Decomp1527b
