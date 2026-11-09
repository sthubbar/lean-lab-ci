/-
Unit U-1622. Split of the pointwise finite character estimate of the doubled system.

The estimate is pointwise in the shift and has three layers, none of which involves an
integral or the arc geometry. First the prime series at a shifted reduced fraction splits
over the residue cosets of the modulus: the phase `exp (-2 pi i a b / q)` is constant on
the coset of `b`, and the damping and the oscillation in the shift stay inside the coset
sum. Second, on the unit cosets alone the transformation matrix is the character table up
to Gauss numbers, so the sum of squared coset sums over the reduced residues is the sum of
the squared character prime sums weighted by the squared Gauss numbers, divided by the
totient; the principal Gauss number has modulus at most one and every other one has
squared modulus at most the modulus. Third, a prime in a coset that is not coprime to the
modulus is divisible by the greatest common divisor of that coset and the modulus, hence
equals one of the prime divisors of the modulus, so at most `log q / log 2` cosets are
nonempty and each of their coset sums has modulus at most one; that is the additive
`totient q log q squared` term the statement allows.

The three layers are the leaves below. The assembly combines them with the elementary
square of a sum bound and the constant `8`. The statement of the target theorem is not
touched: `rational_pointwise_characters1622_split` restates it character for character
and proves it from the three leaves without using the target theorem.
-/
import LeanLab.Linnik1951.SPLIT_doubled_system_characters1622
import LeanLab.Linnik1951.SPLIT_rational_pointwise_characters442

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- LEAF. Step 1 of 3, the residue class splitting identity. The prime series at the
shifted reduced fraction is the sum of its unit coset part and its non unit coset part,
where the coset of residue `b` carries the phase `exp (-2 pi i a b / q)` and the coset
series holds the damping and the oscillation in the shift only. Each coset series is
absolutely convergent, so the regrouping of the prime series by the residue of the prime
modulo `q` is an identity and no estimate occurs. -/
theorem prime_class_split1622 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) (a : ℕ) :
    primeFourier111 N ((a : ℝ) / q + z) =
      (∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) +
      (∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q),
        Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) := by
  exact prime_class_split442 N q hN hq z a

/-- LEAF. Step 2 of 3, unit orthogonality with the Gauss numbers. On the cosets coprime to
the modulus the coset phases form the character table up to Gauss numbers, so the sum over
the reduced residues of the squared moduli of the unit coset sums is at most one over the
totient times the principal character square plus `q` times the nonprincipal character
squares. The principal Gauss number has modulus at most one, every other one has squared
modulus at most the modulus, and the coset sums of the unit part are the character prime
sums of the statement. No integral and no shift estimate occurs. -/
theorem unit_character_orthogonality1622 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q)
    (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
          Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
            Complex.I) *
          (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      1 / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ‖characterPrime280 χ N z‖ ^ 2) := by
  exact unit_character_orthogonality442 N q hN hq z

/-- LEAF. Step 3 of 3, the mass of the residue cosets that are not coprime to the modulus.
A prime in such a coset is divisible by the greatest common divisor of that coset and the
modulus, hence equals one of the prime divisors of the modulus, so only one coset per
prime divisor is nonempty. There are at most `log q / log 2` of those, each nonempty coset
series holds a single damped term and so has modulus at most one, and therefore the sum
over the reduced residues of the squared moduli of the non unit coset sums is at most the
totient times the square of `2 log q`. -/
theorem prime_divisor_class_mass1622 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ‖∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q),
          Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
            Complex.I) *
          (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
            ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
      (q.totient : ℝ) * (2 * Real.log q) ^ 2 := by
  exact prime_divisor_class_mass442 N q hN hq z

/-- The pointwise finite character estimate, from the three layers below it. The splitting
identity writes each prime series as a unit part plus a non unit part, the square of a sum
is at most twice the sum of the squares, and the constants `2` and `8` absorb the two leaf
bounds into the single constant `8`. The statement is unchanged. -/
theorem rational_pointwise_characters1622_split :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q], 1 ≤ N → 2 ≤ q → ∀ z : ℝ,
      (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      B / (q.totient : ℝ) *
        (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * Real.log q ^ 2 := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro N q _ hN hq z
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    have h : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  set U : ℕ → ℂ := fun a =>
    ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
      (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
        ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)
    with hU
  set V : ℕ → ℂ := fun a =>
    ∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q),
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) *
      (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
        ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)
    with hV
  set X : ℝ := ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
      (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖characterPrime280 χ N z‖ ^ 2 with hX
  have hsplit : ∀ a : ℕ, primeFourier111 N ((a : ℝ) / q + z) = U a + V a := by
    intro a
    rw [prime_class_split1622 N q hN hq z a]
  have hstep : ∀ a : ℕ, ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2 ≤
      2 * ‖U a‖ ^ 2 + 2 * ‖V a‖ ^ 2 := by
    intro a
    rw [hsplit a]
    have h1 : ‖U a + V a‖ ≤ ‖U a‖ + ‖V a‖ := norm_add_le _ _
    have h2 : ‖U a + V a‖ ^ 2 ≤ (‖U a‖ + ‖V a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖U a‖ - ‖V a‖)]
  have hsum : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖U a‖ ^ 2) +
        2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖V a‖ ^ 2) := by
    have h1 := Finset.sum_le_sum
      (fun a (_ : a ∈ (range q).filter (fun a => Nat.Coprime a q)) => hstep a)
    have h2 : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          (2 * ‖U a‖ ^ 2 + 2 * ‖V a‖ ^ 2)) =
        2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖U a‖ ^ 2) +
          2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖V a‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    linarith
  have hU2 : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖U a‖ ^ 2) ≤
      1 / (q.totient : ℝ) * X := by
    simpa only [hU, hX] using unit_character_orthogonality1622 N q hN hq z
  have hV2 : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖V a‖ ^ 2) ≤
      (q.totient : ℝ) * (2 * Real.log q) ^ 2 := by
    simpa only [hV] using prime_divisor_class_mass1622 N q hN hq z
  have hX0 : (0 : ℝ) ≤ X := by
    rw [hX]
    have ha : (0 : ℝ) ≤ ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
      positivity
    have hb : (0 : ℝ) ≤ ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖characterPrime280 χ N z‖ ^ 2 :=
      Finset.sum_nonneg (fun χ _ => by positivity)
    have hc : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith
  have hfin : 2 * (1 / (q.totient : ℝ) * X) ≤ 8 / (q.totient : ℝ) * X := by
    have hφ : (0 : ℝ) ≤ 1 / (q.totient : ℝ) := div_nonneg zero_le_one hphi.le
    have ht : (0 : ℝ) ≤ 1 / (q.totient : ℝ) * X := mul_nonneg hφ hX0
    have he : 8 / (q.totient : ℝ) * X = 8 * (1 / (q.totient : ℝ) * X) := by ring
    rw [he]
    linarith
  have h2 : 2 * ((q.totient : ℝ) * (2 * Real.log q) ^ 2) =
      8 * (q.totient : ℝ) * Real.log q ^ 2 := by ring
  have step1 : 2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖U a‖ ^ 2) +
        2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖V a‖ ^ 2) ≤
      2 * (1 / (q.totient : ℝ) * X) +
      2 * ((q.totient : ℝ) * (2 * Real.log q) ^ 2) := by
    linarith [hU2, hV2]
  linarith [hsum, step1, hfin, h2]

#print axioms rational_pointwise_characters1622_split

end LeanLab.Linnik1951
