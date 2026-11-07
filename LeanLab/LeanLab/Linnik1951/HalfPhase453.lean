/-
P0093 page 154 prime series and page 155 equation 2.3 at denominator two.
The exact parity identity retains the contribution of the prime two.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SecondMoment111

namespace LeanLab.Linnik1951

/-- P0093 page 155 equation 2.3 at denominator two, elementary phase step.
Every odd prime has half phase minus one. The prime two has half phase one. -/
theorem prime_half_phase453 (p : Nat.Primes) :
    Complex.exp ((-(2 * Real.pi * (1 / 2 : ℝ) * (p : ℕ)) : ℝ) * Complex.I) =
      if (p : ℕ) = 2 then 1 else -1 := by
  have he : ((-(2 * Real.pi * (1 / 2 : ℝ) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
      ((p : ℕ) : ℂ) * (-((Real.pi : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [he, Complex.exp_nat_mul, Complex.exp_neg_pi_mul_I]
  split_ifs with hp
  · rw [hp]
    norm_num
  · exact (p.property.odd_of_ne_two hp).neg_one_pow

/-- P0093 page 154 prime series and page 155 equation 2.3 at denominator two.
Adding the series at phases alpha and alpha plus one half leaves exactly
 twice the damped term of the prime two. This separates the full prime series term
from the exceptional prime two correction. -/
theorem prime_half_shift453 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    primeFourier111 N (α + 1 / 2) + primeFourier111 N α =
      2 * (Real.exp (-(2 : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * 2) : ℝ) * Complex.I) := by
  classical
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hs := (prime_fourier_summable111 N hN (α + 1 / 2)).tsum_add
    (prime_fourier_summable111 N hN α)
  unfold primeFourier111
  rw [← hs]
  have hterm (p : Nat.Primes) :
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (α + 1 / 2) * (p : ℕ)) : ℝ) * Complex.I) +
        (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I) =
      if p = p2 then 2 * (Real.exp (-(2 : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * 2) : ℝ) * Complex.I) else 0 := by
    have he : ((-(2 * Real.pi * (α + 1 / 2) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
        ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
          ((-(2 * Real.pi * (1 / 2 : ℝ) * (p : ℕ)) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_add, prime_half_phase453]
    by_cases hp : p = p2
    · subst p
      rw [if_pos (rfl : p2 = p2)]
      norm_num [p2]
      ring
    · have hpval : (p : ℕ) ≠ 2 := fun h => hp (Subtype.ext h)
      simp [hp, hpval]
  simp_rw [hterm]
  simp

/-- P0093 page 155 equation 2.3 at denominator two and zero local shift.
The values at zero and one half differ by the exact prime two correction. -/
theorem prime_half_value453 (N : ℕ) (hN : 1 ≤ N) :
    primeFourier111 N (1 / 2) + primeFourier111 N 0 =
      2 * (Real.exp (-(2 : ℝ) / N) : ℂ) := by
  simpa using prime_half_shift453 N hN 0

end LeanLab.Linnik1951
