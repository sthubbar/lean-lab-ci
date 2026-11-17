/-
Split of the saving estimate for the mixed local contribution of the rational
major arcs in this folder.

The estimate bounds the reduced residue sum, over one centred local arc of
radius one over q times N to the one seventh, of the principal prime series
against one translated prime series weighted by the central phase.

The principal prime series is the full prime series minus the prime divisors of
the modulus that the principal character removes. The file cuts the estimate
along exactly that difference:

* the step bounding the full prime series against one translated prime series;
* the step bounding the removed prime divisor correction against the same
  translated series;
* the assembly that writes the principal series back as the difference, splits
  the sum and the arc integral accordingly, and adds the two saving estimates,
  with the constant doubled and the two cutoffs taken to be the larger.

Each leaf is left open for a later pass; the assembly below is complete.
-/
import LeanLab.Linnik1951.SPLIT_mixed_bound520

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- LEAF. Full prime series step. Over one centred local arc of radius one over
q times N to the one seventh, the reduced residue sum of one full prime series
against one translated prime series, weighted by the central phase, is at most
the scale N times the sixth power of the logarithm of N divided by the square
root of q times N to the one seventh. -/
theorem mixed_shifted_prime_part520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          primeFourier111_up111 N z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. Removed prime divisor step. The same sum and the same arc, with the
prime divisors of the modulus that the principal character removes in place of
the first prime series. That correction has one exponentially damped term per
prime divisor of the modulus, so it carries the same saving. -/
theorem mixed_shifted_divisor_part520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- The saving estimate for the mixed local contribution: the principal prime
series is the full prime series minus the removed prime divisor correction, so
the reduced residue sum of the arc integrals splits into the two bounded pieces,
and the triangle inequality plus the doubling of the constant gives the
displayed scale. -/
theorem mixed_shifted_bound520_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨A, hA, NA, hSA⟩ := mixed_shifted_prime_part520 hG
  obtain ⟨B, hB, NB, hSB⟩ := mixed_shifted_divisor_part520 hG
  refine ⟨2 * A + 2 * B, by linarith, max NA NB, ?_⟩
  intro N hN q hq hqQ n hn
  have hNA : NA < N := lt_of_le_of_lt (le_max_left NA NB) hN
  have hNB : NB < N := lt_of_le_of_lt (le_max_right NA NB) hN
  have hN1 : 1 ≤ N :=
    Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le NA) hNA))
  have h1 := hSA N hNA q hq hqQ n hn
  have h2 := hSB N hNB q hq hqQ n hn
  have hsplit :
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) =
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          primeFourier111_up111 N z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) -
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have hFz : Continuous (fun z : ℝ => primeFourier111_up111 N z) :=
      continuous_prime_fourier111_up111 N hN1
    have hFz' : Continuous (fun z : ℝ => primeFourier111_up111 N ((a : ℝ) / q + z)) :=
      (continuous_prime_fourier111_up111 N hN1).comp (by fun_prop)
    have hE : Continuous (fun z : ℝ => Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    have hDz : Continuous (fun z : ℝ =>
        (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I))) := by
      fun_prop
    have hi1 : IntervalIntegrable (fun z : ℝ => primeFourier111_up111 N z *
        primeFourier111_up111 N ((a : ℝ) / q + z) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))
        volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := ((hFz.mul hFz').mul hE).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun z : ℝ =>
        (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
          primeFourier111_up111 N ((a : ℝ) / q + z) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))
        volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := ((hDz.mul hFz').mul hE).intervalIntegrable _ _
    have heq : (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        (primeFourier111_up111 N z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) -
          (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))) =
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        primeFourier111_up111 N z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) -
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) :=
      intervalIntegral.integral_sub hi1 hi2
    rw [← heq]
    apply intervalIntegral.integral_congr
    intro z hz
    simp only [principalPrime520]
    ring
  rw [hsplit]
  have hsN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hsq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrp : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hsN _
  have hs : (0 : ℝ) < Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
    Real.sqrt_pos.2 (mul_pos hsq hrp)
  have hNN : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hsN
  have hL : (0 : ℝ) ≤ Real.log N ^ 6 := by
    have hsq6 : Real.log N ^ 6 = (Real.log N ^ 3) ^ 2 := by ring
    rw [hsq6]
    exact sq_nonneg _
  have hkey :
      (A * (N : ℝ) * Real.log N ^ 6) / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        (B * (N : ℝ) * Real.log N ^ 6) / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
      (2 * A + 2 * B) * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (le_of_lt hs)
    have hAB : A + B ≤ 2 * A + 2 * B := by linarith
    have hNL : (0 : ℝ) ≤ (N : ℝ) * Real.log N ^ 6 := mul_nonneg hNN hL
    nlinarith [mul_le_mul_of_nonneg_right hAB hNL]
  exact le_trans (norm_sub_le _ _) (le_trans (add_le_add h1 h2) hkey)

end LeanLab.Linnik1951
