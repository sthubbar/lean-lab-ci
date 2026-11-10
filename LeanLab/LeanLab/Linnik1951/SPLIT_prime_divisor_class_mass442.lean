/-
Split of `prime_divisor_class_mass442` into three leaves.

The non unit residue classes of the modulus contribute almost nothing to the
squared class mass. A prime whose residue class is not invertible modulo the
modulus shares a prime factor with the modulus and, being prime, is that factor,
so the non unit part of the prime series is supported on the prime divisors of
the modulus alone. Each of those primes contributes one damped exponential of
modulus at most one, there are at most `2 log q` prime divisors, and the square
of that count, summed over the reduced residues of the modulus, is at most the
totient times the square of `2 log q`, which is the right hand side below.

The three leaves record the support and norm bound, the per term damping bound
and the divisor count; the assembly multiplies the per residue bound by the
number of reduced residues. Nothing changes the statement of
`prime_divisor_class_mass442`: the theorem `prime_divisor_class_mass442_split`
restates it character for character and proves it from the leaves without using
the original theorem.
-/
import LeanLab.Linnik1951.SPLIT_rational_pointwise_characters442

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- A noncoprime residue class contains only primes dividing the modulus.
This exact finite identity supplies the omitted classes in page 155 equation 2.3,
and holds for arbitrary complex weights without a convergence premise. -/
theorem nonunit_prime_coset_eq_sum475 (q b : ℕ) (hq : q ≠ 0)
    (hb : ¬ Nat.Coprime b q) (w : ℕ → ℂ) :
    (∑' p : Nat.Primes, if (p : ℕ) % q = b then w p else 0) =
      ∑ p ∈ q.primeFactors, if p % q = b then w p else 0 := by
  classical
  have hsupp (p : Nat.Primes) (hp : (p : ℕ) % q = b) :
      (p : ℕ) ∈ q.primeFactors := by
    have hnc : ¬ Nat.Coprime (p : ℕ) q := by
      intro hc
      apply hb
      rw [← hp]
      exact (ZMod.coprime_mod_iff_coprime _ _).mpr hc
    exact p.property.mem_primeFactors ((p.property.dvd_iff_not_coprime).mpr hnc) hq
  let f : ℕ → ℂ := fun p => if p ∈ q.primeFactors then
    (if p % q = b then w p else 0) else 0
  have hf : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro p hp
    by_cases h : p ∈ q.primeFactors
    · exact ⟨⟨p, Nat.prime_of_mem_primeFactors h⟩, rfl⟩
    · exact False.elim (hp (by simp only [f, ite_eq_right h]))
  calc
    (∑' p : Nat.Primes, if (p : ℕ) % q = b then w p else 0) =
        ∑' p : Nat.Primes, f p := by
      apply tsum_congr
      intro p
      by_cases hp : (p : ℕ) % q = b
      · simp only [f, ite_eq_left (hsupp p hp), ite_eq_left hp]
      · simp only [f, ite_eq_right hp, ite_self]
    _ = ∑' p : ℕ, f p := Nat.Primes.coe_nat_injective.tsum_eq hf
    _ = ∑ p ∈ q.primeFactors, f p :=
      tsum_eq_sum (fun p hp => by simp only [f, ite_eq_right hp])
    _ = ∑ p ∈ q.primeFactors, if p % q = b then w p else 0 := by
      apply sum_congr rfl
      intro p hp
      simp only [f, ite_eq_left hp]

/-- On a nonunit canonical residue class, the only eligible prime is the
residue itself, except that residue zero can contain the modulus as a prime.
This spells out the support assertion behind page 155 equation 2.3. -/
theorem nonunit_prime_residue_value475 (q b : ℕ) (hq : 2 ≤ q) (hb : b < q)
    (hnc : ¬ Nat.Coprime b q) (p : Nat.Primes) (hp : (p : ℕ) % q = b) :
    (p : ℕ) = if b = 0 then q else b := by
  have hdiv : (p : ℕ) ∣ q := p.property.dvd_iff_not_coprime.mpr (by
    intro hc
    apply hnc
    rw [← hp]
    exact (ZMod.coprime_mod_iff_coprime _ _).mpr hc)
  have hle : (p : ℕ) ≤ q := Nat.le_of_dvd (by omega) hdiv
  by_cases hb0 : b = 0
  · rw [if_pos hb0]
    have hqp : q ∣ (p : ℕ) := Nat.dvd_of_mod_eq_zero (hp.trans hb0)
    exact Nat.le_antisymm hle (Nat.le_of_dvd p.property.pos hqp)
  · rw [if_neg hb0]
    have hlt : (p : ℕ) < q := by
      by_contra h
      have heq : (p : ℕ) = q := by omega
      simp [heq] at hp
      exact hb0 hp.symm
    simpa only [Nat.mod_eq_of_lt hlt] using hp

/-- A canonical nonunit prime coset series has at most one term, with any
complex weights. The candidate is the residue, or the modulus for residue zero.
This is an exact form of the support estimate on page 155 equation 2.3. -/
theorem nonunit_prime_coset_eq_term475 (q b : ℕ) (hq : 2 ≤ q) (hb : b < q)
    (hnc : ¬ Nat.Coprime b q) (w : ℕ → ℂ) :
    (∑' p : Nat.Primes, if (p : ℕ) % q = b then w p else 0) =
      if Nat.Prime (if b = 0 then q else b) then w (if b = 0 then q else b) else 0 := by
  classical
  let r : ℕ := if b = 0 then q else b
  have hrmod : r % q = b := by
    dsimp [r]
    split_ifs with h
    · simp [h]
    · exact Nat.mod_eq_of_lt hb
  change _ = if r.Prime then w r else 0
  by_cases hr : r.Prime
  · rw [ite_eq_left hr]
    let p0 : Nat.Primes := ⟨r, hr⟩
    rw [tsum_eq_single p0]
    · exact ite_eq_left hrmod
    · intro p hp
      apply ite_eq_right
      intro hpb
      apply hp
      exact Subtype.ext (nonunit_prime_residue_value475 q b hq hb hnc p hpb)
  · rw [ite_eq_right hr]
    calc
      _ = ∑' _ : Nat.Primes, (0 : ℂ) := by
        apply tsum_congr
        intro p
        apply ite_eq_right
        intro hpb
        have hval : (p : ℕ) = r := nonunit_prime_residue_value475 q b hq hb hnc p hpb
        exact hr (hval ▸ p.property)
      _ = 0 := tsum_zero

/-- LEAF. Step 1 of 3: the support and norm bound for the non unit residue
classes. The coset phase has modulus one, a finite sum of coset series is at
most the sum of their norms, and only the prime divisors of the modulus can have
a residue class that is not invertible modulo the modulus, so the whole non unit
coset sum is dominated by the sum over the prime divisors of the modulus of the
modulus of the damped prime term. No estimate in the number of divisors and no
summation over residues occurs. -/
theorem nonunit_coset_norm_le_primeFactors442 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q)
    (z : ℝ) (a : ℕ) :
    ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖
      ≤ ∑ p ∈ q.primeFactors, ‖(Real.exp (-((p : ℝ) / N)) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)‖ := by
  classical
  let w : ℕ → ℂ := fun p => (Real.exp (-((p : ℝ) / N)) : ℂ) *
    Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)
  let s := (range q).filter (fun b => ¬ Nat.Coprime b q)
  have hcoset (b : ℕ) (hb : b ∈ s) :
      (∑' p : Nat.Primes, if (p : ℕ) % q = b then w p else 0) =
        ∑ p ∈ q.primeFactors, if p % q = b then w p else 0 :=
    nonunit_prime_coset_eq_sum475 q b (by omega) (mem_filter.mp hb).2 w
  change ‖∑ b ∈ s, _‖ ≤ ∑ p ∈ q.primeFactors, ‖w p‖
  calc
    ‖∑ b ∈ s, _‖ ≤ ∑ b ∈ s, ‖Complex.exp
        ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
          (∑' p : Nat.Primes, if (p : ℕ) % q = b then w p else 0)‖ := norm_sum_le _ _
    _ = ∑ b ∈ s, ‖∑ p ∈ q.primeFactors, if p % q = b then w p else 0‖ := by
      apply sum_congr rfl
      intro b hb
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, hcoset b hb]
    _ ≤ ∑ b ∈ s, ∑ p ∈ q.primeFactors, if p % q = b then ‖w p‖ else 0 := by
      apply sum_le_sum
      intro b hb
      simpa only [apply_ite norm, norm_zero] using
        (norm_sum_le (s := q.primeFactors) (f := fun p => if p % q = b then w p else 0))
    _ = ∑ p ∈ q.primeFactors, ∑ b ∈ s, if p % q = b then ‖w p‖ else 0 := sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, ‖w p‖ := by
      apply sum_le_sum
      intro p hp
      rw [sum_ite_eq]
      split_ifs <;> simp [norm_nonneg]

/-- LEAF. Step 2 of 3: the damping bound for a single prime class term. The
exponential damping has modulus `exp (-(p/N))` at most one because the exponent
is nonpositive, and the oscillating factor in the shift has modulus one because
its real part vanishes, so the product has modulus at most one. This holds for
every natural index, including zero, and involves no division in the exponent by
zero since the bound does not need the modulus to be positive. -/
theorem prime_class_term_norm_le_one442 (N : ℕ) (hN : 1 ≤ N) (z : ℝ) (p : ℕ) :
    ‖(Real.exp (-((p : ℝ) / N)) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg p)
    (Nat.cast_nonneg N)))

/-- Each canonical nonunit prime coset has norm at most one. This is the
individual class estimate used in the error on page 155 equation 2.3. -/
theorem nonunit_prime_coset_norm_le_one475 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q)
    (z : ℝ) (b : ℕ) (hb : b < q) (hnc : ¬ Nat.Coprime b q) :
    ‖∑' p : Nat.Primes, if (p : ℕ) % q = b then
      (Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) else 0‖ ≤ 1 := by
  let w : ℕ → ℂ := fun p => (Real.exp (-((p : ℝ) / N)) : ℂ) *
    Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)
  change ‖∑' p : Nat.Primes, if (p : ℕ) % q = b then w p else 0‖ ≤ 1
  rw [nonunit_prime_coset_eq_term475 q b hq hb hnc w]
  by_cases hr : Nat.Prime (if b = 0 then q else b)
  · rw [ite_eq_left hr]
    exact prime_class_term_norm_le_one442 N hN z (if b = 0 then q else b)
  · rw [ite_eq_right hr]
    simp

/-- LEAF. Step 3 of 3: the count of the prime divisors of the modulus. Their
product divides the modulus and each of them is at least two, so the modulus is
at least `2` to the number of them; taking logarithms and using that the
logarithm of two exceeds one half gives the number of prime divisors at most
twice the logarithm of the modulus. This is elementary arithmetic on divisors
and needs no prime series. -/
theorem prime_factors_card_le_log442 (q : ℕ) (hq : 2 ≤ q) :
    ((q.primeFactors.card : ℕ) : ℝ) ≤ 2 * Real.log q := by
  have hpow : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
    have hprod : ∏ p ∈ q.primeFactors, (2 : ℕ) ≤ ∏ p ∈ q.primeFactors, p := by
      exact Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    simpa using hprod
  have hqpow : 2 ^ q.primeFactors.card ≤ q :=
    hpow.trans (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q))
  have hcast : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast hqpow
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ q.primeFactors.card) hcast
  rw [Real.log_pow] at hlog
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc : (0 : ℝ) ≤ (q.primeFactors.card : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- Assembly of `prime_divisor_class_mass442` from the three leaves. Each non
unit coset sum is dominated by the prime divisors of the modulus, each of those
terms has modulus at most one, and there are at most `2 log q` of them, so every
reduced residue contributes at most the square of `2 log q`; summing over the
reduced residues multiplies by the totient. -/
theorem prime_divisor_class_mass442_split (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      (q.totient : ℝ) * (2 * Real.log q) ^ 2 := by
  classical
  have hterm : ∀ a : ℕ, ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ≤ 2 * Real.log q := by
    intro a
    calc ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖
        ≤ ∑ p ∈ q.primeFactors, ‖(Real.exp (-((p : ℝ) / N)) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)‖ :=
          nonunit_coset_norm_le_primeFactors442 N q hN hq z a
      _ ≤ ∑ p ∈ q.primeFactors, (1 : ℝ) :=
          Finset.sum_le_sum (fun p _ => prime_class_term_norm_le_one442 N hN z p)
      _ = ((q.primeFactors.card : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 2 * Real.log q := prime_factors_card_le_log442 q hq
  have hcard : ((range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))
  calc (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2)
      ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), (2 * Real.log q) ^ 2 :=
        Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (norm_nonneg _) (hterm a) 2)
    _ = (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) * (2 * Real.log q) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (q.totient : ℝ) * (2 * Real.log q) ^ 2 := by
        rw [hcard]

#print axioms nonunit_prime_coset_norm_le_one475
#print axioms nonunit_prime_coset_eq_term475
#print axioms nonunit_prime_residue_value475
#print axioms nonunit_prime_coset_eq_sum475
#print axioms nonunit_coset_norm_le_primeFactors442
#print axioms prime_class_term_norm_le_one442
#print axioms prime_factors_card_le_log442
#print axioms prime_divisor_class_mass442_split

end LeanLab.Linnik1951
