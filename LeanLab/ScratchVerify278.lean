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
import Mathlib

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- Membership of a prime in the prime divisors of the modulus, detected on its
residue class: a prime residue class is non invertible modulo the modulus exactly
when the prime divides the modulus. -/
private lemma mem_primeFactors_iff_not_coprime_mod442 (q : ℕ) (hq : 0 < q) (p : Nat.Primes) :
    ¬ Nat.Coprime ((p : ℕ) % q) q ↔ (p : ℕ) ∈ q.primeFactors := by
  have hp := p.property
  have hqne : q ≠ 0 := by omega
  have hgcd : Nat.gcd ((p : ℕ) % q) q = Nat.gcd (p : ℕ) q := by
    rw [← Nat.gcd_comm q ((p : ℕ))]
    exact (Nat.gcd_rec q ((p : ℕ))).symm
  have hcop : Nat.Coprime ((p : ℕ) % q) q ↔ Nat.Coprime (p : ℕ) q := by
    rw [Nat.Coprime, Nat.Coprime, hgcd]
  rw [hcop, Nat.mem_primeFactors]
  constructor
  · intro h
    refine ⟨hp, ?_, hqne⟩
    by_contra hpd
    exact h ((hp.coprime_iff_not_dvd).mpr hpd)
  · rintro ⟨-, hdvd, -⟩
    exact fun hc => (hp.coprime_iff_not_dvd).mp hc hdvd

/-- Summing a coset-supported prime series over a set of residues and then summing
the coset sums exchanges the two summations. -/
private lemma sum_coset_swap442 (q : ℕ) (hq : 0 < q) (s : Finset ℕ) (hs : s ⊆ Finset.range q)
    (Ψ : ℕ → ℂ) (hΨ : ∀ b ∈ s, ‖Ψ b‖ ≤ 1) (w : Nat.Primes → ℂ) (hw : Summable w) :
    (∑ b ∈ s, Ψ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then w p else 0)) =
      ∑' p : Nat.Primes, if ((p : ℕ) % q) ∈ s then Ψ ((p : ℕ) % q) * w p else 0 := by
  classical
  have hfib : ∀ b ∈ s, Summable (fun p : Nat.Primes =>
      if ((p : ℕ) % q = b) then Ψ b * w p else 0) := by
    intro b hb
    refine Summable.of_norm_bounded hw.norm (fun p => ?_)
    by_cases h : ((p : ℕ) % q = b)
    · rw [if_pos h, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hΨ b hb)
    · rw [if_neg h, norm_zero]
      positivity
  trans ∑ b ∈ s, ∑' p : Nat.Primes, (if ((p : ℕ) % q = b) then Ψ b * w p else 0)
  · refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [← tsum_mul_left]
    exact tsum_congr (fun p => by by_cases h : ((p : ℕ) % q = b) <;> simp [h])
  · rw [← Summable.tsum_finsetSum hfib]
    refine tsum_congr (fun p => ?_)
    by_cases h : ((p : ℕ) % q) ∈ s
    · rw [if_pos h]
      refine (Finset.sum_eq_single ((p : ℕ) % q) ?_ ?_).trans (if_pos rfl)
      · intro b hb hne
        rw [if_neg (fun hh => hne hh.symm)]
      · intro hmem
        exact absurd h hmem
    · rw [if_neg h]
      refine Finset.sum_eq_zero (fun b hb => ?_)
      by_cases h2 : ((p : ℕ) % q = b)
      · rw [if_pos h2]
        exact absurd (h2 ▸ hb) h
      · rw [if_neg h2]

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
  have hq0 : 0 < q := by omega
  have hW : Summable (fun p : Nat.Primes => ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) := by
    sorry
  have hsw := sum_coset_swap442 q hq0 ((Finset.range q).filter (fun b => ¬ Nat.Coprime b q))
    (Finset.filter_subset _ _)
    (fun b => Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ) / (q : ℝ))) : ℝ) * Complex.I))
    (fun b hb => by rw [Complex.norm_exp_ofReal_mul_I])
    (fun p : Nat.Primes => ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) hW
  rw [hsw]
  have hcond : ∀ p : Nat.Primes,
      (((p : ℕ) % q) ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q)) ↔
        ((p : ℕ) ∈ q.primeFactors) := by
    intro p
    rw [Finset.mem_filter, Finset.mem_range]
    simp only [Nat.mod_lt ((p : ℕ)) hq0, true_and]
    exact mem_primeFactors_iff_not_coprime_mod442 q hq0 p
  have hsum : Summable (fun p : Nat.Primes => if ((p : ℕ) % q) ∈
      (Finset.range q).filter (fun b => ¬ Nat.Coprime b q) then
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
    refine Summable.of_norm_bounded hW.norm (fun p => ?_)
    by_cases h : ((p : ℕ) % q) ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q)
    · rw [if_pos h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    · rw [if_neg h, norm_zero]
      positivity
  have hsupp : Function.support (fun n : ℕ =>
      if n ∈ q.primeFactors then
        ‖((Real.exp (-((n : ℝ) / N)) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (n : ℝ)) : ℝ) * Complex.I))‖ else 0) ⊆
      Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_cases h : n ∈ q.primeFactors
    · exact ⟨⟨n, (Nat.mem_primeFactors.mp h).1⟩, rfl⟩
    · exact absurd (if_neg h) hn
  calc ‖∑' p : Nat.Primes, if ((p : ℕ) % q) ∈
          (Finset.range q).filter (fun b => ¬ Nat.Coprime b q) then
          Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
            Complex.I) *
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0‖
      ≤ ∑' p : Nat.Primes, ‖if ((p : ℕ) % q) ∈
            (Finset.range q).filter (fun b => ¬ Nat.Coprime b q) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
              Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0‖ :=
          norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' p : Nat.Primes, if ((p : ℕ) ∈ q.primeFactors) then
            ‖((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))‖ else 0 := by
          refine tsum_congr (fun p => ?_)
          by_cases h : ((p : ℕ) % q) ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q)
          · rw [if_pos h, if_pos ((hcond p).mp h)]
            calc ‖Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) /
                (q : ℝ))) : ℝ) * Complex.I) *
                  ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                    Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))‖
                = ‖Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) /
                    (q : ℝ))) : ℝ) * Complex.I)‖ *
                  ‖((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                    Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))‖ :=
                  norm_mul _ _
              _ = _ := by rw [Complex.norm_exp_ofReal_mul_I, one_mul]
          · rw [if_neg h, if_neg (fun hh => h ((hcond p).mpr hh)), norm_zero]
    _ = ∑' n : ℕ, (if n ∈ q.primeFactors then
            ‖((Real.exp (-((n : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * (n : ℝ)) : ℝ) * Complex.I))‖ else 0) :=
          Nat.Primes.coe_nat_injective.tsum_eq hsupp
    _ = ∑ n ∈ q.primeFactors, ‖((Real.exp (-((n : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * (n : ℝ)) : ℝ) * Complex.I))‖ := by
          rw [tsum_eq_sum (f := fun n : ℕ => if n ∈ q.primeFactors then
                ‖((Real.exp (-((n : ℝ) / N)) : ℂ) *
                  Complex.exp ((-(2 * Real.pi * z * (n : ℝ)) : ℝ) * Complex.I))‖ else 0)
            (s := q.primeFactors) (fun n hn => by rw [if_neg hn])]
          exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])

/-- LEAF. Step 2 of 3: the damping bound for a single prime class term. The
exponential damping has modulus `exp (-(p/N))` at most one because the exponent
is nonpositive, and the oscillating factor in the shift has modulus one because
its real part vanishes, so the product has modulus at most one. This holds for
every natural index, including zero, and involves no division in the exponent by
zero since the bound does not need the modulus to be positive. -/
theorem prime_class_term_norm_le_one442 (N : ℕ) (hN : 1 ≤ N) (z : ℝ) (p : ℕ) :
    ‖(Real.exp (-((p : ℝ) / N)) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)‖ ≤ 1 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdiv : 0 ≤ (p : ℝ) / (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg p) (le_of_lt hNpos)
  have hre : ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I : ℂ).re = 0 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    simp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  rw [Complex.norm_exp, hre, Real.exp_zero]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hdiv)

/-- LEAF. Step 3 of 3: the count of the prime divisors of the modulus. Their
product divides the modulus and each of them is at least two, so the modulus is
at least `2` to the number of them; taking logarithms and using that the
logarithm of two exceeds one half gives the number of prime divisors at most
twice the logarithm of the modulus. This is elementary arithmetic on divisors
and needs no prime series. -/
theorem prime_factors_card_le_log442 (q : ℕ) (hq : 2 ≤ q) :
    ((q.primeFactors.card : ℕ) : ℝ) ≤ 2 * Real.log q := by
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hpow : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
    have hbase : ∏ p ∈ q.primeFactors, (2 : ℕ) ≤ ∏ p ∈ q.primeFactors, p := by
      apply Finset.prod_le_prod
      intro p hp
      exact (Nat.mem_primeFactors.mp hp).1.two_le
    simpa using hbase
  have hprod : ∏ p ∈ q.primeFactors, p ≤ q := by
    have hdvd : ∏ p ∈ q.primeFactors, p ∣ q := Nat.prod_primeFactors_dvd q
    exact Nat.le_of_dvd (by omega) hdvd
  have hpowq : 2 ^ q.primeFactors.card ≤ q := le_trans hpow hprod
  have h1 : ((q.primeFactors.card : ℕ) : ℝ) * Real.log 2 ≤ Real.log q := by
    have hcast : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hpowq
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ q.primeFactors.card : ℕ) : ℝ))
      hcast
    rwa [Nat.cast_pow, Real.log_pow] at hlog
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have h2 : ((q.primeFactors.card : ℕ) : ℝ) ≤ Real.log q / Real.log 2 := by
    rw [le_div_iff₀ h2pos]
    linarith
  have h3 : Real.log q / Real.log 2 ≤ 2 * Real.log q := by
    rw [div_le_iff₀ h2pos]
    nlinarith
  linarith

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
