/-
Split of the principal square mass of page 159 before equation 5.3 into three
smaller supplies: the reduction of the local interval of radius at most one half
to the full period, the shift of the half open period to the unit interval, the
Fourier orthogonality of the prime series on the unit interval, and the prime
exponential sum bound that pays the reciprocal logarithm. The assembly below
proves the exact statement of principal_mass435 from those supplies without
using it.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_doubled_system_expansion435

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. The first step of the proof: the local interval is enlarged to the full
period of radius one half. The squared norm kernel is nonnegative and
continuous in the frequency variable, so the integral over the smaller interval
is at most the integral over the larger one. This is the point where the radius r
leaves the statement; what remains is the full period at radius one half. True
also at r equal to zero, where the left side is the empty interval integral and
vanishes. -/
theorem principal_mass435_local_mass (N q : ℕ) (r : ℝ)
    (hN : 1 ≤ N) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
      ∫ z in -(1 / 2)..(1 / 2),
        ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
  sorry

/-- LEAF. The second step of the proof: the half open period of radius one half
carries the same mass as the unit interval. Every summand of the prime series is
a character value times a decaying weight times a complex exponential of period
one in the frequency variable, so the squared norm kernel is periodic with period
one and the two interval integrals agree. This is an identity, not an estimate. -/
theorem principal_mass435_period_shift (N q : ℕ) (hN : 1 ≤ N) :
    (∫ z in -(1 / 2)..(1 / 2),
        ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) =
      ∫ z in (0 : ℝ)..1, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
  sorry

/-- LEAF. The third step of the proof: Fourier orthogonality over one full period
turns the squared norm integral of the prime series into the diagonal sum of the
squared weights. The trivial character takes the value one on every prime, so
each squared weight is the square of the exponential damping, and the
interference terms of distinct primes integrate to zero. This is where the
character disappears from the bound; the radius one half is what makes the
period complete. -/
theorem principal_mass435_orthogonality (N q : ℕ) (hN : 1 ≤ N) :
    (∫ z in (0 : ℝ)..1, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
      ∑' p : Nat.Primes, Real.exp (-(2 * (p : ℝ)) / N) := by
  sorry

/-- LEAF. The fourth step of the proof: the diagonal prime sum is at most a
constant times N over log N. The exponential damping gives geometric decay past
the scale N, and partial summation against the prime count converts the surviving
range into the reciprocal logarithm. This is the only analytic input of the
split and it is why the saving over N is a logarithm rather than a power; it
carries the whole unconditional content of the principal mass. -/
theorem principal_mass435_exponential_sum :
    ∃ P : ℝ, 0 < P ∧ ∀ N : ℕ, 3 ≤ N →
      (∑' p : Nat.Primes, Real.exp (-(2 * (p : ℝ)) / N)) ≤
        P * ((N : ℝ) / Real.log N) := by
  sorry

/-- Page 159 before equation 5.3. The exact statement of principal_mass435,
proved from the four supplies above without using it: enlarge the local interval
to the half open period, shift to the unit interval, apply orthogonality, and pay
the prime sum by the reciprocal logarithm. -/
theorem principal_mass435_split :
    ∃ P : ℝ, 0 < P ∧ ∀ (N q : ℕ) [NeZero q] (r : ℝ), 3 ≤ N → 0 ≤ r → r ≤ 1 / 2 →
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
        P * ((N : ℝ) / Real.log N) := by
  obtain ⟨P, hP, hE⟩ := principal_mass435_exponential_sum
  refine ⟨P, hP, ?_⟩
  intro N q _ r hN hr0 hr
  have hN1 : 1 ≤ N := by omega
  exact (principal_mass435_local_mass N q r hN1 hr0 hr).trans
    ((principal_mass435_period_shift N q hN1).le.trans
      ((principal_mass435_orthogonality N q hN1).trans (hE N hN)))

end LeanLab.Linnik1951
