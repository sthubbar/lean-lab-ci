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
  sorry

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
  sorry

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
