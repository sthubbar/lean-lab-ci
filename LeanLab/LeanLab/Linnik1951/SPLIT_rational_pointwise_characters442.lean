/-
Split of `rational_pointwise_characters442` into three leaves.

The pointwise bound has three layers, none of which uses an integral. First the
prime series at a shifted unit fraction splits over the residue cosets of the
modulus: the phase `exp (-2 pi i a b / q)` is constant on the coset of `b` and
the damped oscillation in the shift stays inside the coset sum. Second, on the
unit cosets alone the transformation matrix is the character table up to Gauss
numbers, so the sum of squares over reduced residues is the sum of the squared
character prime sums weighted by the squared Gauss numbers: the principal Gauss
number has modulus at most one and every other one has modulus `q` up to the
root of unity scale, which gives the totient divided bound. Third, the residue
cosets that are not coprime to the modulus can only contain the prime divisors
of the modulus themselves, so that part of the series is supported on at most
`log q / log 2` cosets with each coset sum of modulus at most one, which is
exactly the additive `totient q log q squared` term that the statement allows.

Leaves 1 to 3 record these three layers; the assembly below combines them with
the elementary square of a sum bound and a constant `8`. Nothing here changes
the statement of `rational_pointwise_characters442`: the theorem
`rational_pointwise_characters442_split` restates it character for character and
proves it from the three leaves without using the original theorem.
-/
import LeanLab.Linnik1951.Decomp442c

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- The phase of the prime term at the shifted reduced fraction is the coset
phase of the residue class of the prime, times the phase of the shift alone, on
the unit circle: only the exponent modulo `2 pi` matters. -/
private lemma circle_exp_coset442 (q : ℕ) (hq : 0 < q) (z : ℝ) (a : ℕ) (p : Nat.Primes) :
    Circle.exp (-(2 * Real.pi * ((a : ℝ) / (q : ℝ) + z) * ((p : ℕ) : ℝ))) =
      Circle.exp (-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ)))) *
        Circle.exp (-(2 * Real.pi * z * ((p : ℕ) : ℝ))) := by
  rw [← Circle.exp_add, Circle.exp_eq_exp]
  set n : ℕ := (p : ℕ) / q with hn
  refine ⟨-((a * n : ℕ) : ℤ), ?_⟩
  have hpq : ((p : ℕ) : ℝ) = (q : ℝ) * (n : ℝ) + ((((p : ℕ) % q : ℕ)) : ℝ) := by
    have h := Nat.div_add_mod (p : ℕ) q
    have h2 : ((q * ((p : ℕ) / q) + (p : ℕ) % q : ℕ) : ℝ) = ((p : ℕ) : ℝ) := by rw [h]
    rw [← hn] at h2
    push_cast at h2
    exact h2.symm
  have hqR : (q : ℝ) ≠ 0 := by
    have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact ne_of_gt hq'
  push_cast
  rw [hpq]
  field_simp
  ring

/-- The same identity for the complex exponential. -/
private lemma exp_arg_coset442 (q : ℕ) (hq : 0 < q) (z : ℝ) (a : ℕ) (p : Nat.Primes) :
    Complex.exp ((-(2 * Real.pi * ((a : ℝ) / (q : ℝ) + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) =
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) := by
  have h := circle_exp_coset442 q hq z a p
  have hcoe : ∀ t : ℝ, Complex.exp ((t : ℝ) * Complex.I) = ((Circle.exp t : Circle) : ℂ) :=
    fun t => (Circle.coe_exp t).symm
  rw [hcoe, hcoe, hcoe]
  simpa using congrArg (fun c : Circle => (c : ℂ)) h

/-- LEAF. Step 1 of 3: the residue coset splitting identity. The prime series at
the shifted reduced fraction is the sum, over the residue cosets of the
modulus, of the coset phase times the coset series, the latter carrying the
damping and the oscillation in the shift but not the shift by the fraction.
Each coset series is absolutely convergent, so the regrouping is an identity and
no estimate is involved. -/
theorem prime_class_split442 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) (a : ℕ) :
    primeFourier111 N ((a : ℝ) / q + z) =
      (∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) +
      (∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) := by
  classical
  have hq0 : 0 < q := by omega
  have hW : Summable (fun p : Nat.Primes => ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) := by
    simpa only [neg_div] using prime_fourier_summable111 N hN z
  have hfib : ∀ b ∈ Finset.range q,
      Summable (fun p : Nat.Primes => if ((p : ℕ) % q = b) then
        (Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) else 0) := by
    intro b hb
    refine Summable.of_norm_bounded hW.norm (fun p => ?_)
    by_cases h : ((p : ℕ) % q = b)
    · rw [if_pos h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    · rw [if_neg h, norm_zero]
      positivity
  have hterm : ∀ p : Nat.Primes,
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) =
        ∑ b ∈ Finset.range q, (if ((p : ℕ) % q = b) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
    intro p
    have hsingle : (∑ b ∈ Finset.range q, (if ((p : ℕ) % q = b) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) =
          Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
              Complex.I) *
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
      refine (Finset.sum_eq_single (s := Finset.range q)
        (f := fun b => (if ((p : ℕ) % q = b) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))
        ((p : ℕ) % q) ?_ ?_).trans (if_pos rfl)
      · intro b hb hne
        rw [if_neg (fun hh => hne hh.symm)]
      · intro hmem
        exfalso
        exact hmem (Finset.mem_range.mpr (Nat.mod_lt ((p : ℕ)) hq0))
    rw [hsingle, exp_arg_coset442 q hq0 z a p, neg_div]
    ring
  have hmain : primeFourier111 N ((a : ℝ) / q + z) =
      ∑ b ∈ Finset.range q, Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
    unfold primeFourier111
    trans ∑' p : Nat.Primes, ∑ b ∈ Finset.range q, (if ((p : ℕ) % q = b) then
            Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
              ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
                Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)
    · exact tsum_congr (fun p => hterm p)
    · rw [Summable.tsum_finsetSum hfib]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [← tsum_mul_left]
      refine tsum_congr (fun p => ?_)
      by_cases h : ((p : ℕ) % q = b) <;> simp [h]
  rw [hmain, ← Finset.sum_filter_add_sum_filter_not (s := Finset.range q)
    (f := fun b => Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))
    (p := fun b => Nat.Coprime b q)]

/-- LEAF. Step 2 of 3: unit character orthogonality with the Gauss numbers. On
the cosets coprime to the modulus the coset phases form the character table up
to Gauss numbers, so the sum of squared coset sums over the reduced residues is
the squared character prime sums weighted by the squared Gauss numbers, divided
by the totient. The principal Gauss number has modulus at most one, every other
one has squared modulus at most the modulus, and the coset sums are exactly the
character prime sums of the statement, the characters themselves vanishing on
the prime divisors of the modulus, so the two sides are identified character by
character. No integral and no shift estimate occurs. -/
theorem unit_character_orthogonality442 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q)
    (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      1 / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2) := by
  sorry

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

/-- The number of distinct prime divisors of the modulus is at most twice its
logarithm, for `q >= 2`. -/
private lemma primeFactors_card_le_log442 (q : ℕ) (hq : 2 ≤ q) :
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

/-- LEAF. Step 3 of 3: the mass of the residue cosets that are not coprime to
the modulus. A prime in such a coset is divisible by the greatest common divisor
of the coset and the modulus, hence equals one of the prime divisors of the
modulus, so only one coset per prime divisor is nonempty. There are at most
`log q / log 2` of those, each coset series has modulus at most one because it
holds a single damped term, and therefore the squared sum over the reduced
residues of the non unit coset sums is at most the totient times the square of
`2 log q`. -/
theorem prime_divisor_class_mass442 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      (q.totient : ℝ) * (2 * Real.log q) ^ 2 := by
  classical
  have hq0 : 0 < q := by omega
  have hW : Summable (fun p : Nat.Primes => ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) := by
    simpa only [neg_div] using prime_fourier_summable111 N hN z
  have hinner : ∀ a : ℕ,
      ‖∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ≤
      ((q.primeFactors.card : ℕ) : ℝ) := by
    intro a
    have hsw := sum_coset_swap442 q hq0 ((Finset.range q).filter (fun b => ¬ Nat.Coprime b q))
      (Finset.filter_subset _ _)
      (fun b => Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I))
      (fun b hb => by rw [Complex.norm_exp_ofReal_mul_I])
      (fun p : Nat.Primes => ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) hW
    rw [hsw]
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
    have hcond : ∀ p : Nat.Primes,
        (((p : ℕ) % q) ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q)) ↔
          ((p : ℕ) ∈ q.primeFactors) := by
      intro p
      rw [Finset.mem_filter, Finset.mem_range]
      simp only [Nat.mod_lt ((p : ℕ)) hq0, true_and]
      exact mem_primeFactors_iff_not_coprime_mod442 q hq0 p
    have hsupp : Function.support (fun n : ℕ =>
        if n ∈ q.primeFactors then Real.exp (-((n : ℝ) / N)) else 0) ⊆
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
            Real.exp (-(((p : ℕ) : ℝ) / N)) else 0 := by
          refine tsum_congr (fun p => ?_)
          by_cases h : ((p : ℕ) % q) ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q)
          · rw [if_pos h, if_pos ((hcond p).mp h), norm_mul, norm_mul,
              Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          · rw [if_neg h, if_neg (fun hh => h ((hcond p).mpr hh)), norm_zero]
      _ = ∑' n : ℕ, (if n ∈ q.primeFactors then Real.exp (-((n : ℝ) / N)) else 0) :=
          Nat.Primes.coe_nat_injective.tsum_eq hsupp
      _ = ∑ n ∈ q.primeFactors, Real.exp (-((n : ℝ) / N)) := by
          rw [tsum_eq_sum (f := fun n : ℕ => if n ∈ q.primeFactors then Real.exp (-((n : ℝ) / N)) else 0)
            (s := q.primeFactors) (fun n hn => by rw [if_neg hn])]
          exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
      _ ≤ ∑ n ∈ q.primeFactors, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          refine Real.exp_le_one_iff.mpr ?_
          have h0 : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
          linarith
      _ = ((q.primeFactors.card : ℕ) : ℝ) := by simp
  have hinner2 : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 ≤
      (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 := by
    intro a ha
    have h1 := hinner a
    nlinarith [norm_nonneg (∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))]
  have hcard : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))
  have hphi : (0 : ℝ) ≤ (q.totient : ℝ) := by positivity
  have hstep : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      (q.totient : ℝ) * (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 := by
    have h1 : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∑ b ∈ (Finset.range q).filter (fun b => ¬ Nat.Coprime b q),
          Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
            Complex.I) *
          (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 := Finset.sum_le_sum hinner2
    have h2 : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          (((q.primeFactors.card : ℕ) : ℝ)) ^ 2) =
        (q.totient : ℝ) * (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
    exact h1.trans_eq h2
  have hω : (((q.primeFactors.card : ℕ) : ℝ)) ≤ 2 * Real.log q :=
    primeFactors_card_le_log442 q hq
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hsq : (((q.primeFactors.card : ℕ) : ℝ)) ^ 2 ≤ (2 * Real.log q) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ((q.primeFactors.card : ℕ) : ℝ) := by positivity
    nlinarith
  exact le_trans hstep (mul_le_mul_of_nonneg_left hsq hphi)

/-- Assembly of `rational_pointwise_characters442` from the three leaves. The
splitting identity writes each prime series as a unit part plus a non unit part,
the square of a sum is at most twice the squares, and the constants `2` and `8`
absorb the two leaf bounds into the single constant `8` of the statement. -/
theorem rational_pointwise_characters442_split :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q], 1 ≤ N → 2 ≤ q → ∀ z : ℝ,
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      B / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * Real.log q ^ 2  := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro N q _ hN hq z
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    have h : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hpoint : ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2 ≤
      2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + 2 * ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 := by
    intro a ha
    rw [prime_class_split442 N q hN hq z a]
    have h1 : ‖(∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) + (∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))‖ ≤
        ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ + ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ := norm_add_le _ _
    have h3 : (‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ + ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖) ^ 2 ≤
        2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + 2 * ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ - ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖)]
    have h2 : ‖(∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) + (∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))‖ ^ 2 ≤
        (‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ + ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith
  have hsum : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) +
        2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) := by
    have h1 := Finset.sum_le_sum hpoint
    have h2 : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          (2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + 2 * ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2)) =
        2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) +
          2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    linarith
  have hU := unit_character_orthogonality442 N q hN hq z
  have hT := prime_divisor_class_mass442 N q hN hq z
  have hX : (0 : ℝ) ≤ ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2 := by
    have ha : (0 : ℝ) ≤ ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
      positivity
    have hb : (0 : ℝ) ≤ ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖characterPrime280 χ N z‖ ^ 2 :=
      Finset.sum_nonneg (fun χ _ => by positivity)
    have hc : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith
  have h1 : 2 * (1 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) ≤
      8 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2) := by
    have hpos : (0 : ℝ) ≤ 1 / (q.totient : ℝ) := div_nonneg zero_le_one hphi.le
    have hm := mul_le_mul_of_nonneg_left (by linarith : 2 * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2) ≤
      8 * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) hpos
    calc 2 * (1 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) =
          (1 / (q.totient : ℝ)) * (2 * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) := by ring
      _ ≤ (1 / (q.totient : ℝ)) * (8 * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) := hm
      _ = 8 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2) := by ring
  have h2 : 2 * ((q.totient : ℝ) * (2 * Real.log q) ^ 2) =
      8 * (q.totient : ℝ) * Real.log q ^ 2 := by ring
  have step1 : 2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) +
        2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      2 * (1 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2)) +
        2 * ((q.totient : ℝ) * (2 * Real.log q) ^ 2) := by
    linarith [hU, hT]
  linarith [hsum, step1, h1, h2]

end LeanLab.Linnik1951
