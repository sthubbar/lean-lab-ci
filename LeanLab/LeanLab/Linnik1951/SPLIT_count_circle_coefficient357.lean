/-
Split of LeanLab/Linnik1951/Decomp357d, theorem count_circle_coefficient357.

The circle coefficient is an integral over the unit interval of a product of
three absolutely convergent Fourier series, one copy of the damped prime
series taken twice and k copies of the damped power-of-two series, times one
exponential of frequency N.  The split is the five steps of its evaluation:
the orthogonal integral at an integral frequency, the pointwise product of the
series, the exchange of the integral of that series with its sum, the value of
every termwise integral, and the count of the tuples whose frequency is N.
The leaves are the hard steps; the assembly is only their combination.
-/
import LeanLab.Linnik1951.Decomp357d

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Step 1 of the proof, the orthogonal integral: the integral over the
unit interval of a complex exponential of an integral frequency is one at
frequency zero and zero at every other integral frequency. -/
theorem integral_exp_two_pi_mul_int357 (m : ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      Complex.exp (((2 * Real.pi * α * (m : ℝ)) : ℝ) * Complex.I)) =
      if m = 0 then 1 else 0 := by
  sorry

/-- LEAF. Step 2 of the proof, the pointwise product: at a fixed point of the
unit interval, one copy of the damped prime series squared times k copies of
the damped power-of-two series times the exponential of frequency N is the
absolutely convergent series over prime pairs and exponent tuples whose
frequencies add up. -/
theorem integrand_eq_tsum357 (k N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
      ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
  sorry

/-- LEAF. Step 3 of the proof, the exchange of the integral with the sum: the
integral over the unit interval of the expanded series of step 2 is the sum
over the same index set of the termwise integrals, each taken by step 1, so
each term survives exactly when its frequency is N. -/
theorem integral_tsum_swap357 (k N : ℕ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)) =
      ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * (if ((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1)) = N then (1 : ℂ) else 0) := by
  sorry

/-- LEAF. Step 4 of the proof, the count: at frequency N the damping weight of
every surviving tuple is exp of minus one, and the surviving tuples are in
bijection with the ordered representations counted by
representationCount111, so the sum over them is exp of minus one times that
count. -/
theorem tsum_indicator_eq_count357 (k N : ℕ) (hN : 1 ≤ N) :
    (∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * (if ((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1)) = N then (1 : ℂ) else 0)) =
      (Real.exp (-1) : ℂ) * (representationCount111 k N : ℂ) := by
  sorry

/-- The circle coefficient, assembled from the four leaves of this file: integrate
the expanded product, swap the integral with the sum, evaluate every termwise
integral, and count the surviving tuples. -/
theorem count_circle_coefficient357_split (k N : ℕ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1, primeFourier111 N α ^ 2 * powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) = (Real.exp (-1) : ℂ) * (representationCount111 k N : ℂ) := by
  have hexp : (∫ α in Set.Icc (0 : ℝ) 1, primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
      Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) =
      ∫ α in Set.Icc (0 : ℝ) 1,
        ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
          (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro α _
    exact integrand_eq_tsum357 k N hN α
  rw [hexp, integral_tsum_swap357 k N hN, tsum_indicator_eq_count357 k N hN]

end LeanLab.Linnik1951
