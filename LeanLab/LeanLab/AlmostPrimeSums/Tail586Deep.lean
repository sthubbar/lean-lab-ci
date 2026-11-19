import LeanLab.AlmostPrimeSums.Tail586

/-!
AI wrote this Lean code for CODEX task586. Goldbach is open.
The large count Rankin regime of the lower Rosser moment.
The explicit mass threshold is retained. The three sealed leaves stay open.
Source: Iwaniec, Rosser's sieve, p. 198 before equation 8.4,
https://doi.org/10.4064/aa-36-2-171-202.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real BoundingSieve

/-- A squarefree divisor defect is at most two to its prime factor count.
This is the finite coefficient bound used in the Rankin estimate on
Iwaniec p. 198 before equation 8.4. -/
theorem rosserDefect_le_two_pow_card586 (D : ℝ) (b : Bool) {n : ℕ}
    (hn : Squarefree n) : rosserDefect D b n ≤ (2 : ℝ) ^ n.primeFactors.card := by
  classical
  by_cases hn1 : n = 1
  · subst n
    cases b <;> simp [rosserDefect, rosserWeight, decPrimes]
  have hc : n.divisors.card = 2 ^ n.primeFactors.card := by
    rw [Nat.card_divisors hn.ne_zero]
    calc
      _ = ∏ _p ∈ n.primeFactors, (2 : ℕ) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [Nat.factorization_eq_one_of_squarefree hn
          (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
      _ = _ := by simp
  have habs : |∑ d ∈ n.divisors, rosserWeight D b d| ≤ (n.divisors.card : ℝ) := by
    calc
      _ ≤ ∑ d ∈ n.divisors, |rosserWeight D b d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) :=
        Finset.sum_le_sum fun d _ => abs_rosserWeight_le_one D b d
      _ = _ := by simp
  rw [hc, Nat.cast_pow, Nat.cast_ofNat] at habs
  cases b
  · simpa [rosserDefect, hn1] using (neg_le_abs _).trans habs
  · simpa [rosserDefect, hn1] using (le_abs_self _).trans habs

/-- The Selberg prime count generating sum is an exact finite Euler
product. This is the finite generating series normalization used in
Iwaniec p. 198 before equation 8.4. -/
theorem selberg_card_generating586 (s : BoundingSieve) (T : ℝ) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * T ^ n.primeFactors.card) =
      ∏ p ∈ s.prodPrimes.primeFactors, (1 + T * s.selbergTerms p) := by
  classical
  calc
    _ = ∑ n ∈ s.prodPrimes.divisors,
        ∏ p ∈ n.primeFactors, T * s.selbergTerms p := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        s.selbergTerms_isMultiplicative.prod_primeFactors
          (s.prodPrimes_squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hn).1)]
      ring
    _ = ∑ A ∈ s.prodPrimes.primeFactors.powerset,
        ∏ p ∈ A, T * s.selbergTerms p :=
      sum_divisors_primeFactors_eq_powerset s
        (fun A => ∏ p ∈ A, T * s.selbergTerms p)
    _ = _ := (Finset.prod_one_add _).symm

/-- Nonnegative local Selberg factors give the exponential envelope of
the exact generating product. Derived scalar step in Iwaniec p. 198
before equation 8.4. -/
theorem selberg_card_generating_le_exp586 (s : BoundingSieve) (T : ℝ)
    (hT : 0 ≤ T) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * T ^ n.primeFactors.card) ≤
      exp (T * ∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p) := by
  rw [selberg_card_generating586]
  calc
    _ ≤ ∏ p ∈ s.prodPrimes.primeFactors, exp (T * s.selbergTerms p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hpos := s.selbergTerms_pos (Nat.dvd_of_mem_primeFactors hp)
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (T * s.selbergTerms p)
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

/-- LEAF. The large divisor moment has exponential decay once the level
ratio dominates the explicit total Selberg prime mass. This is an
unbounded cutoff regime, not the full uniform leaf. Derived Rankin
count estimate from Iwaniec p. 198 before equation 8.4. -/
theorem rosser_large_divisor_mass_exp586 (s : BoundingSieve) (D z σ : ℝ)
    (hz : 1 < z) (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hscale : 2 + (2 * exp 2) *
      (∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p) ≤ σ) (b : Bool) :
    (∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => z ^ (σ - 1) < n),
      s.selbergTerms n * rosserDefect D b n) ≤ exp (-σ) := by
  classical
  let U : ℝ := 2 * exp 2
  let E : ℝ := exp (-2 * (σ - 1))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hE : 0 ≤ E := (exp_pos _).le
  have hterm : ∀ n ∈ s.prodPrimes.divisors.filter
      (fun n : ℕ => z ^ (σ - 1) < n),
      s.selbergTerms n * rosserDefect D b n ≤
        E * (s.selbergTerms n * U ^ n.primeFactors.card) := by
    intro n hn
    obtain ⟨hnP, hnlarge⟩ := Finset.mem_filter.mp hn
    have hnD := (Nat.mem_divisors.mp hnP).1
    have hsq := s.prodPrimes_squarefree.squarefree_of_dvd hnD
    have hcount := primeFactors_card_gt_of_rpow_lt586 hsq hz
      (fun p hp => hP p (Nat.primeFactors_mono hnD s.prodPrimes_ne_zero hp)) hnlarge
    have he : 1 ≤ E * exp (2 * (n.primeFactors.card : ℝ)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have hpow : (2 : ℝ) ^ n.primeFactors.card ≤ E * U ^ n.primeFactors.card := by
      calc
        _ ≤ (2 : ℝ) ^ n.primeFactors.card *
            (E * exp (2 * (n.primeFactors.card : ℝ))) :=
          le_mul_of_one_le_right (by positivity) he
        _ = _ := by
          dsimp [U]
          rw [mul_pow, ← Real.exp_nat_mul]
          rw [mul_comm (n.primeFactors.card : ℝ) 2]
          ring
    calc
      _ ≤ s.selbergTerms n * (2 : ℝ) ^ n.primeFactors.card :=
        mul_le_mul_of_nonneg_left (rosserDefect_le_two_pow_card586 D b hsq)
          (s.selbergTerms_pos hnD).le
      _ ≤ s.selbergTerms n * (E * U ^ n.primeFactors.card) :=
        mul_le_mul_of_nonneg_left hpow (s.selbergTerms_pos hnD).le
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => z ^ (σ - 1) < n),
        E * (s.selbergTerms n * U ^ n.primeFactors.card) := Finset.sum_le_sum hterm
    _ = E * ∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => z ^ (σ - 1) < n),
        s.selbergTerms n * U ^ n.primeFactors.card := (Finset.mul_sum ..).symm
    _ ≤ E * ∑ n ∈ s.prodPrimes.divisors,
        s.selbergTerms n * U ^ n.primeFactors.card := by
      apply mul_le_mul_of_nonneg_left _ hE
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n hn _ => mul_nonneg (s.selbergTerms_pos (Nat.mem_divisors.mp hn).1).le
          (pow_nonneg hU _))
    _ ≤ E * exp (U * ∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p) :=
      mul_le_mul_of_nonneg_left (selberg_card_generating_le_exp586 s U hU) hE
    _ = exp (-2 * (σ - 1) + U *
        ∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p) := (Real.exp_add ..).symm
    _ ≤ exp (-σ) := Real.exp_le_exp.mpr (by dsimp [U] at *; linarith)

/-- The linear density condition bounds the total local Selberg mass
by an explicit multiple of the prime density logarithm. Derived local
factor normalization for the Rankin regime in Iwaniec p. 198 before
equation 8.4. No uniform bound in z is asserted. -/
theorem sum_selberg_prime_le_density586 (s : BoundingSieve) (K z : ℝ)
    (hK : 0 ≤ K) (hz : 2 < z)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (hden : LinearDensity s K) :
    (∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p) ≤
      (1 + K / log 2) * (log (log z / log 2) + K / log 2) := by
  classical
  let A : ℝ := 1 + K / log 2
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlocal : ∀ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p ≤ A * s.nu p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hlog : log 2 ≤ log (p : ℝ) := log_le_log (by norm_num) hp2
    have hinv : (1 - s.nu p)⁻¹ ≤ A := by
      have hfactor := linearDensity_prime_factor_bound s K hK hden hp
      have hquot := div_le_div_of_nonneg_left hK hl2 hlog
      dsimp [A]
      linarith
    rw [s.selbergTerms_apply, hprime.primeFactors, Finset.prod_singleton]
    exact (mul_le_mul_of_nonneg_left hinv
      (s.nu_pos_of_prime p hprime (Nat.dvd_of_mem_primeFactors hp)).le).trans_eq (by ring)
  have hfilter : s.prodPrimes.primeFactors.filter
      (fun p : ℕ => (2 : ℝ) ≤ p ∧ (p : ℝ) < z) = s.prodPrimes.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact ⟨by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le, hP p hp⟩
  have hsum := linearDensity_interval_sum s K hK hden 2 z le_rfl hz
  rw [hfilter] at hsum
  calc
    _ ≤ ∑ p ∈ s.prodPrimes.primeFactors, A * s.nu p := Finset.sum_le_sum hlocal
    _ = A * ∑ p ∈ s.prodPrimes.primeFactors, s.nu p := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hA

/-- LEAF. The exact large divisor lower moment in the sealed split has
constant one in the regime where the level ratio dominates the displayed
logarithmic local mass threshold. The cutoff z is unbounded. This is a
proved subregime, not the full large divisor leaf. Derived Rankin regime
of Iwaniec p. 198 before equation 8.4. -/
theorem lower_defect_moment_large_n_rankin586 (s : BoundingSieve) (K z D : ℝ)
    (hK : 0 ≤ K) (hz : 2 < z)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (hden : LinearDensity s K)
    (hscale : 2 + (2 * exp 2) * (1 + K / log 2) *
      (log (log z / log 2) + K / log 2) ≤ log D / log z) :
    (∑ n ∈ (s.prodPrimes.divisors.filter
        (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card)).filter
        (fun n : ℕ => ¬ ((n : ℝ) ≤ z ^ (log D / log z - 1))),
      s.selbergTerms n * rosserDefect D false n) ≤ exp (-(log D / log z)) := by
  classical
  have hmass := sum_selberg_prime_le_density586 s K z hK hz hP hden
  have hscale' : 2 + (2 * exp 2) *
      (∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p) ≤ log D / log z := by
    have hh := mul_le_mul_of_nonneg_left hmass (by positivity : (0 : ℝ) ≤ 2 * exp 2)
    nlinarith only [hh, hscale]
  have hsub : ((s.prodPrimes.divisors.filter
      (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card)).filter
      (fun n : ℕ => ¬ ((n : ℝ) ≤ z ^ (log D / log z - 1)))) ⊆
      s.prodPrimes.divisors.filter (fun n : ℕ => z ^ (log D / log z - 1) < n) := by
    intro n hn
    obtain ⟨hn, hlarge⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, lt_of_not_ge hlarge⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ =>
    mul_nonneg (s.selbergTerms_pos (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1).1).le
      (rosserDefect_nonneg D false n))).trans
    (rosser_large_divisor_mass_exp586 s D z (log D / log z) (by linarith) hP hscale' false)

/-- LEAF. The full restricted defect tail has constant exp two when
the level ratio dominates the displayed local mass threshold. This is
uniform in the unbounded cutoff z within this explicit regime and
covers both parities. It does not assert the remaining uniform stopping
estimate. Derived Rankin regime of Iwaniec p. 198 before equation 8.4. -/
theorem rosser_defect_tail_rankin586 (s : BoundingSieve) (K z D : ℝ)
    (hK : 0 ≤ K) (hz : 2 < z) (hD : 0 < D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (hden : LinearDensity s K)
    (hscale : 4 + (2 * exp 2) * (1 + K / log 2) *
      (log (log z / log 2) + K / log 2) ≤ log D / log z) (b : Bool) :
    (∑ n ∈ s.prodPrimes.divisors.filter
        (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card),
      s.selbergTerms n * rosserDefect D b n) ≤ exp 2 * exp (-(log D / log z)) := by
  classical
  have hz0 : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hmass := sum_selberg_prime_le_density586 s K z hK hz hP hden
  have hscale' : 2 + (2 * exp 2) *
      (∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p) ≤ log D / log z - 2 := by
    have hh := mul_le_mul_of_nonneg_left hmass (by positivity : (0 : ℝ) ≤ 2 * exp 2)
    nlinarith only [hh, hscale]
  have hsub : s.prodPrimes.divisors.filter
      (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card) ⊆
      s.prodPrimes.divisors.filter (fun n : ℕ => z ^ (log D / log z - 2 - 1) < n) := by
    intro n hn
    obtain ⟨hnP, hncut, hncard⟩ := Finset.mem_filter.mp hn
    have hnD := (Nat.mem_divisors.mp hnP).1
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hnD)
    refine Finset.mem_filter.mpr ⟨hnP, ?_⟩
    apply (Real.rpow_lt_iff_lt_log hz0 hn0).mpr
    have hlog := log_le_log hD hncut
    rw [Real.log_mul hn0.ne' (pow_ne_zero _ hz0.ne'), Real.log_pow] at hlog
    have hratio : log D / log z * log z = log D := div_mul_cancel₀ _ hlz.ne'
    norm_num only [Nat.cast_ofNat] at hlog
    nlinarith only [hlog, hratio, hlz]
  calc
    _ ≤ ∑ n ∈ s.prodPrimes.divisors.filter
        (fun n : ℕ => z ^ (log D / log z - 2 - 1) < n),
        s.selbergTerms n * rosserDefect D b n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ =>
        mul_nonneg (s.selbergTerms_pos
          (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1).1).le (rosserDefect_nonneg D b n))
    _ ≤ exp (-(log D / log z - 2)) :=
      rosser_large_divisor_mass_exp586 s D z (log D / log z - 2)
        (by linarith) hP hscale' b
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The explicit Rankin threshold is unbounded in z for fixed K.
Thus the proved Rankin regime does not exhaust the sealed uniform leaf.
Derived parameter limitation of the generating estimate on Iwaniec
p. 198 before equation 8.4. This does not refute a moment leaf. -/
theorem rankin_threshold_tendsto_atTop586 (K : ℝ) (hK : 0 ≤ K) :
    Filter.Tendsto (fun z : ℝ => 4 + (2 * exp 2) * (1 + K / log 2) *
      (log (log z / log 2) + K / log 2)) Filter.atTop Filter.atTop := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hdiv := Real.tendsto_log_atTop.atTop_div_const hl2
  have hlog := Real.tendsto_log_atTop.comp hdiv
  have hsum := Filter.tendsto_atTop_add_const_right _ (K / log 2) hlog
  have hc : 0 < (2 * exp 2) * (1 + K / log 2) := by positivity
  exact Filter.tendsto_atTop_add_const_left _ 4 (hsum.const_mul_atTop hc)

/-- In the explicit Rankin regime the existing finite Rosser construction
has all coefficient and support properties and relative exponential
error with constant exp two. This is an unbounded cutoff subregime
of Iwaniec p. 177 Theorem 4, derived from the finite normalization and
the generating estimate on p. 198 before equation 8.4. The displayed
threshold is retained and the unrestricted fundamental lemma stays open. -/
theorem fundamental_lemma_rankin586 (s : BoundingSieve) (K z D : ℝ)
    (hK : 0 ≤ K) (hz : 2 < z) (hD : z ^ 10 ≤ D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (hden : LinearDensity s K)
    (hscale : 4 + (2 * exp 2) * (1 + K / log 2) *
      (log (log z / log 2) + K / log 2) ≤ log D / log z) :
    ∃ lp lm : ℕ → ℝ,
      (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
      (∀ d, lp d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
      (∀ d, lm d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
      IsUpperMoebius lp ∧
      (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) ∧
      |s.mainSum lp - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
        exp 2 * exp (-(log D / log z)) *
          ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ∧
      |s.mainSum lm - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
        exp 2 * exp (-(log D / log z)) *
          ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  have hzD : z ≤ D := by
    calc
      z = z ^ 1 := by simp
      _ ≤ z ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ D := hD
  have hD0 : 0 < D := (by linarith : 0 < z).trans_le hzD
  have hmoment : ∀ b : Bool,
      (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D b n) ≤
        exp 2 * exp (-(log D / log z)) := by
    intro b
    rw [rosser_defect_moment_eq_tail_many_primes s D z hz.le hD hP]
    exact rosser_defect_tail_rankin586 s K z D hK hz hD0 hP hden hscale b
  have hV : 0 ≤ ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_nonneg fun p hp => (sub_pos.mpr
      (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp))).le
  have herr : ∀ b : Bool,
      |s.mainSum (rosserWeight D b) - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
        exp 2 * exp (-(log D / log z)) *
          ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
    intro b
    rw [rosser_mainSum_error_eq]
    exact (mul_le_mul_of_nonneg_left (hmoment b) hV).trans_eq (by ring)
  obtain ⟨lp, lm, hb, hp1, hm1, hsp, hsm, hu, hl, hmp, hmm⟩ :=
    rosser_fundamental_weights s z D hzD (by linarith) hP
  refine ⟨lp, lm, hb, hp1, hm1, hsp, hsm, hu, hl, ?_, ?_⟩
  · simpa only [hmp] using herr true
  · simpa only [hmm] using herr false

end LeanLab.AlmostPrimeSums.Decomp1527b
