import LeanLab.AlmostPrimeSums.RosserCard
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
AI wrote this Lean code for CODEX task586. Goldbach is open.
Finite prerequisites for the lower Rosser defect moment.
These statements do not assert a uniform exponential moment estimate.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real BoundingSieve

/-- LEAF. A squarefree number above a real power of z has more prime
factors than that exponent when all its prime factors are below z.
Derived counting step for Heath Brown p. 34, the ordered prime product
display, and BJS p. 10 equation 28. -/
theorem primeFactors_card_gt_of_rpow_lt586 {n : ℕ} (hn : Squarefree n)
    {z t : ℝ} (hz : 1 < z)
    (hP : ∀ p ∈ n.primeFactors, (p : ℝ) < z) (hlarge : z ^ t < n) :
    t < (n.primeFactors.card : ℝ) := by
  have hprod : (n : ℝ) ≤ z ^ n.primeFactors.card := by
    calc
      _ = ∏ p ∈ n.primeFactors, (p : ℝ) := by
        rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
      _ ≤ ∏ _p ∈ n.primeFactors, z :=
        Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p) (fun p hp => (hP p hp).le)
      _ = _ := by simp
  exact (Real.rpow_lt_rpow_left_iff hz).mp
    (hlarge.trans_le (by simpa only [Real.rpow_natCast] using hprod))

/-- LEAF. A removed squarefree Rosser coefficient has a failed gate at
an index of the selected parity. Heath Brown p. 34, the defining ordered
prime product display, and BJS p. 10 equation 28. -/
theorem exists_failed_rosser_gate586 {d : ℕ} (hd : Squarefree d)
    (D : ℝ) (b : Bool) (hremoved : rosserWeight D b d ≠
      (ArithmeticFunction.moebius d : ℝ)) :
    ∃ m < (decPrimes d).length, (b = true ↔ m % 2 = 0) ∧
      D ≤ (((decPrimes d).take m).prod : ℝ) *
        ((decPrimes d).getD m 0 : ℝ) ^ 3 := by
  have hfail : ¬ ∀ m < (decPrimes d).length, (b = true ↔ m % 2 = 0) →
      (((decPrimes d).take m).prod : ℝ) *
        ((decPrimes d).getD m 0 : ℝ) ^ 3 < D := by
    intro h
    exact hremoved (ite_eq_left ⟨hd, h⟩)
  push Not at hfail
  exact hfail

/-- LEAF. At a failed gate the product of the leading m plus one primes
exceeds D divided by z squared. This keeps the actual gate, rather than
just the cardinality of the complete divisor. Derived from Heath Brown
p. 34, the ordered prime product display, and BJS p. 10 equation 28. -/
theorem failed_gate_leading_product586 {d m : ℕ} {D z : ℝ}
    (hD : 0 < D) (hz : 0 < z) (hm : m < (decPrimes d).length)
    (hP : ∀ p ∈ d.primeFactors, (p : ℝ) < z)
    (hgate : D ≤ (((decPrimes d).take m).prod : ℝ) *
      ((decPrimes d).getD m 0 : ℝ) ^ 3) :
    D / z ^ 2 < (((decPrimes d).take (m + 1)).prod : ℝ) := by
  have hpz : ((decPrimes d).getD m 0 : ℝ) < z := by
    apply hP
    have hh : (decPrimes d).getD m 0 ∈ decPrimes d := by
      rw [List.getD_eq_getElem _ 0 hm]
      exact List.getElem_mem hm
    simpa [decPrimes] using hh
  have hp0 : (0 : ℝ) ≤ (decPrimes d).getD m 0 := Nat.cast_nonneg _
  have hsq : ((decPrimes d).getD m 0 : ℝ) ^ 2 < z ^ 2 := by nlinarith
  have hprefix : 0 < (((decPrimes d).take m).prod : ℝ) *
      ((decPrimes d).getD m 0 : ℝ) := by
    have hpos : 0 < (((decPrimes d).take m).prod : ℝ) *
        ((decPrimes d).getD m 0 : ℝ) ^ 3 := hD.trans_le hgate
    have hnonneg : (0 : ℝ) ≤ ((decPrimes d).take m).prod := Nat.cast_nonneg _
    nlinarith
  apply (div_lt_iff₀ (sq_pos_of_pos hz)).mpr
  rw [List.prod_take_succ _ _ hm, Nat.cast_mul, ← List.getD_eq_getElem _ 0 hm]
  calc
    D ≤ _ := hgate
    _ = ((((decPrimes d).take m).prod : ℝ) *
        ((decPrimes d).getD m 0 : ℝ)) * ((decPrimes d).getD m 0 : ℝ) ^ 2 := by ring
    _ < _ := mul_lt_mul_of_pos_left hsq hprefix

/-- LEAF. The normalized Selberg mass of divisors with at least m prime
factors in A is at most the mth density power sum on A divided by m factorial.
This is a derived finite union bound for the unordered prime sum on
Opera de Cribro p. 67 preceding equation 6.65. The Euler product on the
left is essential. No uniform bound on the prime density sum is assumed. -/
theorem selberg_mass_many_primes_in586 (s : BoundingSieve)
    (A : Finset ℕ) (hA : A ⊆ s.prodPrimes.primeFactors) (m : ℕ) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
      (∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => m ≤ (n.primeFactors ∩ A).card),
        s.selbergTerms n) ≤
      (∑ p ∈ A, s.nu p) ^ m / (m.factorial : ℝ) := by
  classical
  let P := A
  let Q := P.powersetCard m
  let V := ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)
  have hnu : ∀ p ∈ P, 0 ≤ s.nu p := fun p hp =>
    (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors (hA hp))
      (Nat.dvd_of_mem_primeFactors (hA hp))).le
  have hV : 0 ≤ V := Finset.prod_nonneg fun p hp =>
    (sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp))).le
  have hprod_dvd : ∀ {T : Finset ℕ} {n : ℕ}, T ⊆ n.primeFactors →
      (∏ p ∈ T, p) ∣ n := by
    intro T n hT
    exact (Finset.prod_dvd_prod_of_subset T n.primeFactors id hT).trans
      (Nat.prod_primeFactors_dvd n)
  have hpoint : ∀ n ∈ s.prodPrimes.divisors,
      (if m ≤ (n.primeFactors ∩ A).card then s.selbergTerms n else 0) ≤
        ∑ T ∈ Q, if (∏ p ∈ T, p) ∣ n then s.selbergTerms n else 0 := by
    intro n hn
    have hwn : 0 ≤ s.selbergTerms n :=
      (s.selbergTerms_pos (Nat.mem_divisors.mp hn).1).le
    by_cases hc : m ≤ (n.primeFactors ∩ A).card
    · obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hc
      have hTP : T ⊆ P := hT.trans Finset.inter_subset_right
      have hTn : T ⊆ n.primeFactors := hT.trans Finset.inter_subset_left
      have hTQ : T ∈ Q := Finset.mem_powersetCard.mpr ⟨hTP, hcard⟩
      simpa only [hc, ite_eq_left, hprod_dvd hTn] using
        (Finset.single_le_sum (f := fun T =>
          if (∏ p ∈ T, p) ∣ n then s.selbergTerms n else 0)
          (fun _ _ => by split_ifs <;> positivity) hTQ)
    · simp only [hc]
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  have hunion : V *
      (∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => m ≤ (n.primeFactors ∩ A).card),
        s.selbergTerms n) ≤ ∑ T ∈ Q, s.nu (∏ p ∈ T, p) := by
    calc
      _ = V * ∑ n ∈ s.prodPrimes.divisors,
          if m ≤ (n.primeFactors ∩ A).card then s.selbergTerms n else 0 := by
        rw [Finset.sum_filter]
      _ ≤ V * ∑ n ∈ s.prodPrimes.divisors,
          ∑ T ∈ Q, if (∏ p ∈ T, p) ∣ n then s.selbergTerms n else 0 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) hV
      _ = ∑ T ∈ Q, V * ∑ n ∈ s.prodPrimes.divisors,
          if (∏ p ∈ T, p) ∣ n then s.selbergTerms n else 0 := by
        rw [Finset.sum_comm, Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        exact eulerProduct_mul_selbergTerms_multiples s
          (hprod_dvd ((Finset.mem_powersetCard.mp hT).1.trans hA))
  have hfact := LeanLab.PNTSieve.Bonferroni.factorial_mul_esymm_le
    (fun p => max (s.nu p) 0) (fun _ => le_max_right _ _) P m
  have hsum : (∑ p ∈ P, max (s.nu p) 0) = ∑ p ∈ P, s.nu p :=
    Finset.sum_congr rfl fun p hp => max_eq_left (hnu p hp)
  have he : LeanLab.PNTSieve.Bonferroni.esymm (fun p => max (s.nu p) 0) P m =
      ∑ T ∈ Q, s.nu (∏ p ∈ T, p) := by
    apply Finset.sum_congr rfl
    intro T hT
    have hTP := (Finset.mem_powersetCard.mp hT).1
    rw [s.nu_mult.map_prod_of_subset_primeFactors s.prodPrimes T (hTP.trans hA)]
    exact Finset.prod_congr rfl fun p hp => max_eq_left (hnu p (hTP hp))
  rw [hsum, he] at hfact
  exact hunion.trans ((le_div_iff₀ (by positivity : (0 : ℝ) < m.factorial)).mpr
    (by simpa only [mul_comm] using hfact))

/-- LEAF. Taking every sieve prime as the selected set gives the normalized
factorial bound for the full prime factor count. Derived finite form of the
unordered prime sum on Opera de Cribro p. 67 before equation 6.65. -/
theorem selberg_mass_many_primes_le_power_sum586 (s : BoundingSieve) (m : ℕ) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
      (∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => m ≤ n.primeFactors.card),
        s.selbergTerms n) ≤
      (∑ p ∈ s.prodPrimes.primeFactors, s.nu p) ^ m / (m.factorial : ℝ) := by
  have hh := selberg_mass_many_primes_in586 s s.prodPrimes.primeFactors
    Finset.Subset.rfl m
  have he : s.prodPrimes.divisors.filter (fun n : ℕ =>
      m ≤ (n.primeFactors ∩ s.prodPrimes.primeFactors).card) =
      s.prodPrimes.divisors.filter (fun n : ℕ => m ≤ n.primeFactors.card) := by
    apply Finset.filter_congr
    intro n hn
    rw [Finset.inter_eq_left.mpr (Nat.primeFactors_mono
      (Nat.mem_divisors.mp hn).1 s.prodPrimes_ne_zero)]
  rw [he] at hh
  exact hh

/-- LEAF. The density condition supplies the explicit factorial mass
parameter on a prime interval. Derived normalized interval version of
Opera de Cribro p. 67, the two bounds before equation 6.65, using the
lab density condition with its K divided by log w error. -/
theorem linearDensity_selberg_mass_interval586 (s : BoundingSieve)
    (K w z : ℝ) (hK : 0 ≤ K) (hden : LinearDensity s K)
    (hw : 2 ≤ w) (hwz : w < z) (m : ℕ) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
      (∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => m ≤
        (n.primeFactors ∩ s.prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).card), s.selbergTerms n) ≤
      (log (log z / log w) + K / log w) ^ m / (m.factorial : ℝ) := by
  let A := s.prodPrimes.primeFactors.filter
    (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hsum := linearDensity_interval_sum s K hK hden w z hw hwz
  have hmass0 : 0 ≤ ∑ p ∈ A, s.nu p := Finset.sum_nonneg fun p hp =>
    (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le
  exact (selberg_mass_many_primes_in586 s A (Finset.filter_subset _ _) m).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hmass0 hsum m) (by positivity))

/-- The Euler product cannot be discarded from the normalized factorial
bound. A single prime with density one half has Selberg mass one on
nontrivial divisors, but prime density sum one half. Derived check of the
normalization in Opera de Cribro p. 67 before equation 6.65. -/
theorem unnormalized_factorial_shortcut_fails586 :
    ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ LinearDensity s (log 2) ∧
      (∑ p ∈ s.prodPrimes.primeFactors, s.nu p) <
        ∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => 1 ≤ n.primeFactors.card),
          s.selbergTerms n := by
  obtain ⟨s, hP, _, hnu, hden, _⟩ := single_prime_density_instance
  have hd : (2 : ℕ).divisors = {1, 2} := by decide
  refine ⟨s, hP, hden, ?_⟩
  norm_num [hP, hd, s.selbergTerms_apply, hnu, Nat.prime_two.primeFactors,
    Finset.sum_filter]

/-- LEAF. Stirling bounds a factorial mass by its geometric envelope.
Opera de Cribro p. 68 equations 6.71 to 6.75. This evaluation requires
the mass parameter M explicitly and asserts no uniform bound on it. -/
theorem factorial_mass_le_geometric586 (M : ℝ) (hM : 0 ≤ M)
    (m : ℕ) (hm : m ≠ 0) :
    M ^ m / (m.factorial : ℝ) ≤ (exp 1 * M / m) ^ m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hroot : 1 ≤ sqrt (2 * Real.pi * m) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.pi_gt_three]
  have hfactorial : ((m : ℝ) / exp 1) ^ m ≤ (m.factorial : ℝ) :=
    (le_mul_of_one_le_left (by positivity) hroot).trans (Stirling.le_factorial_stirling m)
  calc
    _ ≤ M ^ m / ((m : ℝ) / exp 1) ^ m :=
      div_le_div_of_nonneg_left (pow_nonneg hM _) (by positivity) hfactorial
    _ = _ := by
      rw [← div_pow]
      congr 1
      field_simp

/-- LEAF. A factorial mass decays at least as exp of minus m once
m dominates exp two times its mass parameter. This is the scalar
Stirling evaluation behind Opera de Cribro p. 68 equation 6.75. -/
theorem factorial_mass_le_exp586 (M : ℝ) (hM : 0 ≤ M)
    (m : ℕ) (hm : m ≠ 0) (hscale : exp 2 * M ≤ m) :
    M ^ m / (m.factorial : ℝ) ≤ exp (-(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hexp : exp (-1) * exp 2 = exp 1 := by rw [← exp_add]; norm_num
  have hratio : exp 1 * M / m ≤ exp (-1) := by
    apply (div_le_iff₀ hm0).mpr
    have hh := mul_le_mul_of_nonneg_left hscale (exp_pos (-1)).le
    simpa only [← mul_assoc, hexp] using hh
  calc
    _ ≤ (exp 1 * M / m) ^ m := factorial_mass_le_geometric586 M hM m hm
    _ ≤ (exp (-1)) ^ m := pow_le_pow_left₀ (by positivity) hratio m
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

/-- The direct factorial series criterion in Opera de Cribro p. 67
equations 6.65 and 6.67 fails at beta equal to two and dimension one.
This rejects that proof route and does not negate a Rosser moment leaf. -/
theorem beta_two_factorial_criterion_fails586 :
    1 < (log 3 / 2) * exp (1 + log 3 / 2) := by
  have hlog : 1 < log 3 := by linarith [Real.log_three_gt_d9]
  have he : 2 < exp (1 + log 3 / 2) :=
    Real.exp_one_gt_two.trans (Real.exp_lt_exp.mpr (by linarith))
  nlinarith

/-- LEAF. In the fundamental lemma range a failed gate forces its
leading prime product above D to the power four fifths. Derived power
form of Heath Brown p. 34, the ordered prime product display, and
BJS p. 10 equation 28. The exact finite gate is retained. -/
theorem failed_gate_leading_product_rpow586 {d m : ℕ} {D z : ℝ}
    (hz : 2 ≤ z) (hD : z ^ 10 ≤ D) (hm : m < (decPrimes d).length)
    (hP : ∀ p ∈ d.primeFactors, (p : ℝ) < z)
    (hgate : D ≤ (((decPrimes d).take m).prod : ℝ) *
      ((decPrimes d).getD m 0 : ℝ) ^ 3) :
    D ^ (4 / 5 : ℝ) < (((decPrimes d).take (m + 1)).prod : ℝ) := by
  have hz0 : 0 < z := by linarith
  have hD0 : 0 < D := (pow_pos hz0 10).trans_le hD
  have hprefix := failed_gate_leading_product586 hD0 hz0 hm hP hgate
  have hq : 0 < D / z ^ 2 := div_pos hD0 (sq_pos_of_pos hz0)
  have hp0 : (0 : ℝ) < ((decPrimes d).take (m + 1)).prod := hq.trans hprefix
  have hlogD : 10 * log z ≤ log D := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using log_le_log (pow_pos hz0 10) hD
  have hlogprefix := log_lt_log hq hprefix
  rw [Real.log_div hD0.ne' (pow_ne_zero _ hz0.ne'), Real.log_pow] at hlogprefix
  rw [Real.rpow_def_of_pos hD0]
  calc
    exp (log D * (4 / 5)) < exp (log (((decPrimes d).take (m + 1)).prod : ℝ)) :=
      exp_lt_exp.mpr (by norm_num only [Nat.cast_ofNat] at hlogprefix; linarith)
    _ = _ := exp_log hp0

/-- LEAF. Combining the interval density power sum with Stirling gives
an exponential bound when the explicit mass parameter is dominated by
the count. Derived finite normalization between Opera de Cribro p. 67
before equation 6.65 and p. 68 equation 6.75. -/
theorem linearDensity_selberg_mass_interval_exp586 (s : BoundingSieve)
    (K w z : ℝ) (hK : 0 ≤ K) (hden : LinearDensity s K)
    (hw : 2 ≤ w) (hwz : w < z) (m : ℕ) (hm : m ≠ 0)
    (hscale : exp 2 * (log (log z / log w) + K / log w) ≤ m) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
      (∑ n ∈ s.prodPrimes.divisors.filter (fun n : ℕ => m ≤
        (n.primeFactors ∩ s.prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)).card), s.selbergTerms n) ≤
      exp (-(m : ℝ)) := by
  have hsum := linearDensity_interval_sum s K hK hden w z hw hwz
  have hmass0 : 0 ≤ ∑ p ∈ s.prodPrimes.primeFactors.filter
      (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z), s.nu p :=
    Finset.sum_nonneg fun p hp => (s.nu_pos_of_prime p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le
  exact (linearDensity_selberg_mass_interval586 s K w z hK hden hw hwz m).trans
    (factorial_mass_le_exp586 _ (hmass0.trans hsum) m hm hscale)

/-- Even with the density condition, a local Selberg factor need not be
strictly below one. The density nu at a prime is below one, whereas
the corresponding Selberg factor is nu divided by one minus nu.
Derived normalization check for Opera de Cribro p. 67. -/
theorem selberg_prime_not_lt_one586 :
    ∃ s : BoundingSieve, LinearDensity s (log 2) ∧
      ∃ p ∈ s.prodPrimes.primeFactors, 1 ≤ s.selbergTerms p := by
  obtain ⟨s, hP, _, hnu, hden, _⟩ := single_prime_density_instance
  refine ⟨s, hden, 2, by simp [hP, Nat.prime_two.primeFactors], ?_⟩
  norm_num [s.selbergTerms_apply, hnu, Nat.prime_two.primeFactors]

/-- LEAF. A finite factorial tail has its exponential Rankin bound for
any multiplier at least one. This is the finite generating series step
in Iwaniec, Rosser's sieve, p. 198 before equation 8.4.
https://doi.org/10.4064/aa-36-2-171-202. -/
theorem factorial_tail_le_rankin586 (M L : ℝ) (hM : 0 ≤ M) (hL : 1 ≤ L) (m N : ℕ) :
    (∑ r ∈ (range N).filter (fun r => m ≤ r), M ^ r / (r.factorial : ℝ)) ≤
      exp (L * M) / L ^ m := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  apply (le_div_iff₀ (pow_pos hL0 m)).mpr
  calc
    _ = ∑ r ∈ (range N).filter (fun r => m ≤ r),
        L ^ m * M ^ r / (r.factorial : ℝ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ r ∈ (range N).filter (fun r => m ≤ r),
        (L * M) ^ r / (r.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [mul_pow]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hL (Finset.mem_filter.mp hr).2) (pow_nonneg hM r))
        (by positivity)
    _ ≤ ∑ r ∈ range N, (L * M) ^ r / (r.factorial : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ ≤ exp (L * M) := Real.sum_le_exp_of_nonneg (mul_nonneg hL0.le hM) N

/-- Enlarging the density constant preserves the density condition.
This supplies the elementary K at least two normalization in Iwaniec,
Rosser's sieve, p. 171 equation 1.3 without altering the lab definition.
https://doi.org/10.4064/aa-36-2-171-202. -/
theorem linearDensity_mono_constant586 (s : BoundingSieve) {K L : ℝ}
    (hKL : K ≤ L) (hden : LinearDensity s K) : LinearDensity s L := by
  intro w z hw hwz
  have hlw : 0 < log w := log_pos (by linarith)
  have hlz : 0 ≤ log z := log_nonneg (by linarith)
  exact (hden w z hw hwz).trans (mul_le_mul_of_nonneg_left
    (by linarith [div_le_div_of_nonneg_right hKL hlw.le])
    (div_nonneg hlz hlw.le))

end LeanLab.AlmostPrimeSums.Decomp1527b
