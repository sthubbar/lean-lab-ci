/-
Split of mellin_lnL_expansion1622 into four leaves. The transfer identity is cut
at the two places where its content actually sits, plus the bookkeeping that
joins them:

* the Euler product step, which turns the logarithm of the L-function on the
  line into a double series over primes and exponents (the only step that uses
  the zero hypothesis and the only one that mentions the L-function);
* the Mellin step, which evaluates the Mellin integral of that double series as
  the same double series carrying the exponential damping at each prime power
  (no L-function, no character prime sum, no zero hypothesis);
* the size estimate that makes the double series absolutely summable, which is
  what allows the two steps above to be applied termwise;
* the bookkeeping step, which splits the double series at exponent one and
  identifies that slice with the character prime sum, leaving the exponents at
  least two reindexed by their offset from two.

The assembly at the end has no sorry and does not use mellin_lnL_expansion1622.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_mellin_transfer1622

namespace LeanLab.Linnik1951

/-- LEAF. Euler product step. Under the hypothesis on the zeros, the logarithm of
the L-function of a nonprincipal character at the point one half plus one over
the logarithm of N plus i t is the double series over all primes and all
exponents at least one, the coefficient of an exponent being the character value
at the corresponding prime power divided by that exponent, times the negative
power of the prime power. No Mellin integral and no character prime sum occur
here. -/
theorem log_L_prime_power_series1622 (hG : LeanLab.DERZ1997.GRH) :
    ∀ N : ℕ, 2 ≤ N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ t : ℝ, Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))
        = ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 N t)) := by
  sorry

/-- LEAF. Mellin step. The Mellin integral of the prime power double series is
the same double series with every term carrying the prime power damping and the
character twist at that prime power, the pair of parameters being the reciprocal
of N and twice pi alpha. This is the termwise evaluation of the integral against
the kernel and carries no L-function, no character prime sum and no zero
hypothesis. -/
theorem mellin_prime_power_series1622 :
    ∀ N : ℕ, 2 ≤ N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, ∀ α : ℝ,
      mellinU1622 N
          (fun t : ℝ => ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 N t))) α
        = ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (m + 1) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (m + 1))) : ℝ) * Complex.I) := by
  sorry

/-- LEAF. Size estimate. The damped prime power double series is absolutely
summable on the product of the primes and the exponents: the character factor has
modulus at most one, the exponent factor is at most one over the exponent, and
the damping falls off geometrically in the exponent. This is an estimate only,
with no identity, no Mellin integral and no zero hypothesis. -/
theorem prime_power_series_summable1622 (N : ℕ) (hN : 2 ≤ N)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (α : ℝ) :
    Summable (fun x : Nat.Primes × ℕ =>
      ‖((x.2 : ℂ) + 1)⁻¹ * χ ((x.1 : ℕ) ^ (x.2 + 1)) *
        (Real.exp (-(((x.1 : ℕ) : ℝ) ^ (x.2 + 1) / (N : ℝ))) : ℂ) *
          Complex.exp
            ((-(2 * Real.pi * α * (((x.1 : ℕ) : ℝ) ^ (x.2 + 1))) : ℝ) * Complex.I)‖) := by
  sorry

/-- LEAF. Bookkeeping step. The damped prime power double series splits at the
exponent one: that slice is exactly the character prime sum, and the remaining
exponents, shifted by two, are the tail of the statement. A sum rearrangement
only, with no analysis. -/
theorem prime_power_split1622 (N : ℕ) (hN : 2 ≤ N)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (α : ℝ) :
    ∑' p : Nat.Primes, ∑' m : ℕ,
        ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (m + 1) / (N : ℝ))) : ℂ) *
            Complex.exp
              ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (m + 1))) : ℝ) * Complex.I)
      = characterPrime280 χ N α +
          ∑' p : Nat.Primes, ∑' k : ℕ,
            (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)) := by
  sorry

/-- The Mellin integral only sees the coefficient as a function of the line
parameter, so two coefficients that agree at every point give the same integral. -/
private lemma mellinU1622_congr_local (N : ℕ) (M M' : ℝ → ℂ) (α : ℝ)
    (h : ∀ t : ℝ, M t = M' t) : mellinU1622 N M α = mellinU1622 N M' α := by
  simp only [mellinU1622]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [h t]

/-- The Euler product step and the Mellin step evaluate the two sides against
each other, and the bookkeeping step separates the character prime sum from the
prime power tail of exponents at least two. -/
theorem mellin_lnL_expansion1622_split (hG : LeanLab.DERZ1997.GRH) :
    ∀ N : ℕ, 2 ≤ N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ,
      characterPrime280 χ N α -
          mellinU1622 N
            (fun t : ℝ => Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))) α
        = -∑' p : Nat.Primes, ∑' k : ℕ,
            (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)) := by
  intro N hN q hq χ hχ α
  haveI : NeZero q := hq
  have h1 : mellinU1622 N
        (fun t : ℝ => Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))) α
      = mellinU1622 N
          (fun t : ℝ => ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 N t))) α :=
    mellinU1622_congr_local N _ _ α
      (fun t => log_L_prime_power_series1622 hG N hN q χ hχ t)
  have h2 := mellin_prime_power_series1622 N hN q χ α
  have h3 := prime_power_split1622 N hN q χ α
  rw [h1, h2, h3]
  ring

end LeanLab.Linnik1951
