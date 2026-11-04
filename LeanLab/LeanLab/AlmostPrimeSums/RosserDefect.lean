import LeanLab.AlmostPrimeSums.Decomp1527b
import LeanLab.AlmostPrimeSums.RosserTransform

/-!
AI wrote this Lean code for CODEX task258. Goldbach is open.
The finite Rosser defect and its positive Selberg average refine the
fundamental lemma into its upper and lower analytic error estimates.
Sources: Heath Brown, Lectures on sieves, pp. 31 to 35,
https://arxiv.org/abs/math/0209360, and BJS p. 10 equation 28,
https://arxiv.org/abs/2207.09452.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real ArithmeticFunction BoundingSieve

/-- The nonnegative upper or lower divisor sum defect of the existing
Rosser weights. Derived finite quantity from Heath Brown pp. 31 to 32. -/
noncomputable def rosserDefect (D : ℝ) (upper : Bool) (n : ℕ) : ℝ :=
  if upper then
    (∑ d ∈ n.divisors, rosserWeight D upper d) - (if n = 1 then 1 else 0)
  else
    (if n = 1 then 1 else 0) - ∑ d ∈ n.divisors, rosserWeight D upper d

/-- Each Rosser defect is nonnegative, with no condition on the level.
Derived finite sign fact from Heath Brown pp. 31 to 32. -/
theorem rosserDefect_nonneg (D : ℝ) (upper : Bool) (n : ℕ) :
    0 ≤ rosserDefect D upper n := by
  cases upper
  · simpa [rosserDefect] using sub_nonneg.mpr (rosser_lower_le D n)
  · simpa [rosserDefect] using sub_nonneg.mpr (rosser_upper_isUpperMoebius D n)

/-- Below the small coefficient cutoff, the full divisor sum defect vanishes.
Derived support localization from Heath Brown p. 34 and BJS p. 10 equation 28. -/
theorem rosserDefect_eq_zero_of_small (D z : ℝ) (hz : 0 ≤ z) (upper : Bool) {n : ℕ}
    (hP : ∀ p ∈ n.primeFactors, (p : ℝ) ≤ z) (hsmall : (n : ℝ) * z ^ 2 < D) :
    rosserDefect D upper n = 0 := by
  classical
  by_cases hn : n = 0
  · subst n; simp [rosserDefect]
  have hsum : (∑ d ∈ n.divisors, rosserWeight D upper d) =
      if n = 1 then 1 else 0 := by
    have hmu := congrArg (fun f : ArithmeticFunction ℝ => f n)
      (coe_moebius_mul_coe_zeta (R := ℝ))
    rw [coe_mul_zeta_apply] at hmu
    calc
      _ = ∑ d ∈ n.divisors, (moebius d : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdn := (Nat.mem_divisors.mp hd).1
        apply rosserWeight_eq_moebius_of_small D z hz upper
        · intro p hp
          exact hP p (Nat.primeFactors_mono hdn hn hp)
        · have hle : (d : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn
          exact (mul_le_mul_of_nonneg_right hle (sq_nonneg z)).trans_lt hsmall
      _ = _ := by simpa only [intCoe_apply, one_apply] using hmu
  cases upper <;> simp [rosserDefect, hsum]

/-- Both main term errors are exactly V times their nonnegative Selberg
defect moments. Derived finite identity for Heath Brown pp. 31 to 35. -/
theorem rosser_mainSum_error_eq (s : BoundingSieve) (D : ℝ) (upper : Bool) :
    |s.mainSum (rosserWeight D upper) -
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p))| =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n := by
  have hsign := mainSum_eulerProduct_signs s (rosserWeight D true) (rosserWeight D false)
    (fun n _ => rosser_upper_isUpperMoebius D n) (fun n _ => rosser_lower_le D n)
  cases upper
  · rw [abs_of_nonpos (sub_nonpos.mpr hsign.2), mainSum_sub_eulerProduct_eq]
    simp only [rosserDefect, Bool.false_eq_true, ↓reduceIte]
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr hsign.1), mainSum_sub_eulerProduct_eq]
    rfl

/-- The upper main sum is V times one plus its defect moment. The lower
main sum is V times one minus its defect moment.
Derived finite normalization for Heath Brown p. 35. -/
theorem rosser_mainSum_eq_defect (s : BoundingSieve) (D : ℝ) (upper : Bool) :
    s.mainSum (rosserWeight D upper) =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (if upper then
          1 + ∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n
        else
          1 - ∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n) := by
  have hsign := mainSum_eulerProduct_signs s (rosserWeight D true) (rosserWeight D false)
    (fun n _ => rosser_upper_isUpperMoebius D n) (fun n _ => rosser_lower_le D n)
  have he := rosser_mainSum_error_eq s D upper
  cases upper
  · rw [abs_of_nonpos (sub_nonpos.mpr hsign.2)] at he
    simp only [Bool.false_eq_true, ↓reduceIte]
    nlinarith [he]
  · rw [abs_of_nonneg (sub_nonneg.mpr hsign.1)] at he
    simp only [↓reduceIte]
    nlinarith [he]

/-- An upper Rosser main term bound is equivalent to the normalized defect
bound with one subtracted from its coefficient.
Derived formulation of the upper main term on Heath Brown p. 35. -/
theorem rosser_upper_mainSum_iff_defect (s : BoundingSieve) (D U : ℝ) :
    s.mainSum (rosserWeight D true) ≤
        (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) * U ↔
      (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D true n) ≤ U - 1 := by
  have hV : 0 < ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_pos fun p hp => sub_pos.mpr
      (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  rw [rosser_mainSum_eq_defect]
  simp only [↓reduceIte, mul_le_mul_iff_right₀ hV]
  constructor <;> intro hh <;> linarith

/-- A lower Rosser main term bound is equivalent to a defect bound with
its coefficient subtracted from one. Derived finite normalization for the
lower sieve conclusion on Heath Brown p. 36. -/
theorem rosser_lower_mainSum_iff_defect (s : BoundingSieve) (D L : ℝ) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) * L ≤
        s.mainSum (rosserWeight D false) ↔
      (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D false n) ≤ 1 - L := by
  have hV : 0 < ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_pos fun p hp => sub_pos.mpr
      (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  rw [rosser_mainSum_eq_defect]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_le_mul_iff_right₀ hV]
  constructor <;> intro hh <;> linarith

/-- The defect moment is supported on the same explicit large divisor tail,
while keeping the cancellation inside each divisor sum.
Derived support identity for Heath Brown pp. 31 to 35 and BJS p. 10. -/
theorem rosser_defect_moment_eq_tail (s : BoundingSieve) (D z : ℝ) (hz : 0 ≤ z)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (upper : Bool) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D upper n) =
      ∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2),
        s.selbergTerms n * rosserDefect D upper n := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases ht : D ≤ (n : ℝ) * z ^ 2
  · simp [ht]
  · have he := rosserDefect_eq_zero_of_small D z hz upper
      (fun p hp => (hP p (Nat.primeFactors_mono (Nat.mem_divisors.mp hn).1
        s.prodPrimes_ne_zero hp)).le) (lt_of_not_ge ht)
    simp [ht, he]

/-- Both existing Rosser main sums are exact once P times z squared is below
the level. This is a finite regime, not the uniform analytic estimate.
Derived from the cube cutoff on Heath Brown p. 34. -/
theorem rosser_mainSum_exact_of_prod_bound (s : BoundingSieve) (D z : ℝ) (hz : 0 ≤ z)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hsmall : (s.prodPrimes : ℝ) * z ^ 2 < D) (upper : Bool) :
    s.mainSum (rosserWeight D upper) =
      ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  have he := rosser_mainSum_error_eq s D upper
  have hzero : ∑ n ∈ s.prodPrimes.divisors,
      s.selbergTerms n * rosserDefect D upper n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnp := (Nat.mem_divisors.mp hn).1
    have hle : (n : ℝ) ≤ s.prodPrimes := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) hnp
    rw [rosserDefect_eq_zero_of_small D z hz upper
      (fun p hp => (hP p (Nat.primeFactors_mono hnp s.prodPrimes_ne_zero hp)).le)
      ((mul_le_mul_of_nonneg_right hle (sq_nonneg z)).trans_lt hsmall), mul_zero]
  rw [hzero, mul_zero] at he
  exact sub_eq_zero.mp (abs_eq_zero.mp he)

/-- At most seven sifting primes make both Rosser main sums exact throughout
the fundamental lemma range. No density condition is needed for this finite
regime. Derived from the cube cutoff on Heath Brown p. 34. -/
theorem rosser_mainSum_exact_of_card_le_seven (s : BoundingSieve) (D z : ℝ)
    (hz : 2 ≤ z) (hD : z ^ 10 ≤ D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hcard : s.prodPrimes.primeFactors.card ≤ 7) (upper : Bool) :
    s.mainSum (rosserWeight D upper) =
      ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  have hz0 : 0 ≤ z := by linarith
  have hprod : (s.prodPrimes : ℝ) ≤ z ^ s.prodPrimes.primeFactors.card := by
    calc
      _ = ∏ p ∈ s.prodPrimes.primeFactors, (p : ℝ) := by
        rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree]
      _ ≤ ∏ _p ∈ s.prodPrimes.primeFactors, z :=
        Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p) (fun p hp => (hP p hp).le)
      _ = _ := by simp
  have hprod7 : (s.prodPrimes : ℝ) ≤ z ^ 7 :=
    hprod.trans (pow_le_pow_right₀ (by linarith) hcard)
  apply rosser_mainSum_exact_of_prod_bound s D z hz0 hP
  calc
    _ ≤ z ^ 7 * z ^ 2 := mul_le_mul_of_nonneg_right hprod7 (sq_nonneg z)
    _ = z ^ 9 := by ring
    _ < z ^ 10 := by
      have hpos : 0 < z ^ 9 := pow_pos (by linarith) _
      calc
        z ^ 9 < z ^ 9 * z := lt_mul_of_one_lt_right hpos (by linarith)
        _ = z ^ 10 := by ring
    _ ≤ D := hD

/-- Above a cutoff whose logarithm absorbs K, the density product has any
prescribed multiplicative loss. Derived from HR p. 142 and BJS p. 10 equation 29. -/
theorem linearDensity_uniform_above (s : BoundingSieve) (K eps w₀ : ℝ)
    (h : LinearDensity s K) (heps : 0 ≤ eps) (hw₀ : 2 ≤ w₀)
    (hcut : K ≤ eps * log w₀) (w w' : ℝ) (hw : w₀ ≤ w) (hww' : w < w') :
    (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'),
      (1 - s.nu p)⁻¹) ≤ log w' / log w * (1 + eps) := by
  have hw2 : 2 ≤ w := hw₀.trans hw
  have hlw : 0 < log w := log_pos (by linarith)
  have hlog : log w₀ ≤ log w := log_le_log (by linarith) hw
  have hK : K / log w ≤ eps := (div_le_iff₀ hlw).mpr
    (hcut.trans (mul_le_mul_of_nonneg_left hlog heps))
  exact (h w w' hw2 hww').trans (mul_le_mul_of_nonneg_left
    (by linarith) (div_nonneg (log_nonneg (by linarith)) hlw.le))

/-- The interval density mass and inverse product control the relative
factorial error of an adjacent Brun block. This is a derived quantitative
block input from HR p. 142 and the lab BrunBlocksRel recursion. -/
theorem linearDensity_interval_block_rho (s : BoundingSieve) (K : ℝ) (hK : 0 ≤ K)
    (h : LinearDensity s K) (w w' : ℝ) (hw : 2 ≤ w) (hww' : w < w') (r : ℕ) :
    let Q := s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w')
    let M := log (log w' / log w) + K / log w
    let R := log w' / log w * (1 + K / log w)
    LeanLab.PNTSieve.Bonferroni.rho s.nu (Q, r, r + 1) ≤
      max (M ^ (r + 1) / (r + 1).factorial) (M ^ (r + 2) / (r + 2).factorial) * R := by
  let Q := s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w')
  let M := log (log w' / log w) + K / log w
  let R := log w' / log w * (1 + K / log w)
  change LeanLab.PNTSieve.Bonferroni.rho s.nu (Q, r, r + 1) ≤
    max (M ^ (r + 1) / (r + 1).factorial) (M ^ (r + 2) / (r + 2).factorial) * R
  have hmass : (∑ p ∈ Q, s.nu p) ≤ M := linearDensity_interval_sum s K hK h w w' hw hww'
  have hmass0 : 0 ≤ ∑ p ∈ Q, s.nu p := Finset.sum_nonneg fun p hp =>
    (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le
  have hM : 0 ≤ M := hmass0.trans hmass
  have hV : 0 < ∏ p ∈ Q, (1 - s.nu p) := Finset.prod_pos fun p hp =>
    sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1))
  have hinv : (∏ p ∈ Q, (1 - s.nu p))⁻¹ ≤ R := by
    simpa only [Finset.prod_inv_distrib] using h w w' hw hww'
  have hE : ∀ j : ℕ, LeanLab.PNTSieve.Bonferroni.truncErr Q s.nu j ≤
      M ^ (j + 1) / (j + 1).factorial := by
    intro j
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hmass0 hmass _)
      (Nat.cast_nonneg _)
  unfold LeanLab.PNTSieve.Bonferroni.rho
  simp only
  rw [div_eq_mul_inv]
  apply mul_le_mul
  · exact max_le_max (hE r) (by simpa [Nat.add_assoc] using hE (r + 1))
  · exact hinv
  · exact (inv_pos.mpr hV).le
  · exact le_max_of_le_left (by positivity)

end LeanLab.AlmostPrimeSums.Decomp1527b
