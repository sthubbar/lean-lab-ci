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
  sorry

/-- LEAF. Step 2 of 3: the damping bound for a single prime class term. The
exponential damping has modulus `exp (-(p/N))` at most one because the exponent
is nonpositive, and the oscillating factor in the shift has modulus one because
its real part vanishes, so the product has modulus at most one. This holds for
every natural index, including zero, and involves no division in the exponent by
zero since the bound does not need the modulus to be positive. -/
theorem prime_class_term_norm_le_one442 (N : ℕ) (hN : 1 ≤ N) (z : ℝ) (p : ℕ) :
    ‖(Real.exp (-((p : ℝ) / N)) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)‖ ≤ 1 := by
  sorry

/-- LEAF. Step 3 of 3: the count of the prime divisors of the modulus. Their
product divides the modulus and each of them is at least two, so the modulus is
at least `2` to the number of them; taking logarithms and using that the
logarithm of two exceeds one half gives the number of prime divisors at most
twice the logarithm of the modulus. This is elementary arithmetic on divisors
and needs no prime series. -/
theorem prime_factors_card_le_log442 (q : ℕ) (hq : 2 ≤ q) :
    ((q.primeFactors.card : ℕ) : ℝ) ≤ 2 * Real.log q := by
  sorry

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

#print axioms prime_divisor_class_mass442_split

end LeanLab.Linnik1951
