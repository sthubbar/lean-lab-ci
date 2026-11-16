/-
Split of the mixed local contribution estimate for the rational major arcs of
the circle-method decomposition in this folder.

The mixed contribution is the cross term of the exact square expansion of the
local prime series: twice the principal coefficient times the principal prime
series times the residue error, integrated over one centred local arc of radius
one over q times N to the one seventh, and summed over the reduced residues.

Two remarks fix the shape of the split.

* The cross term cannot be cut into its two algebraic summands.  At modulus one
  the principal prime series equals the full prime series, so the sum over the
  reduced residues of the principal part against one full prime factor and the
  diagonal term are equal and both of size about N over the square of the
  logarithm, while their difference is identically zero.  Each summand is
  therefore larger than the claimed scale and only their signed combination is
  small; a per summand leaf would be false.

* The unit modulus is settled inside the parent file by the vanishing of the
  mixed integral, so the estimate concerns moduli from two upwards.

The split therefore cuts the estimate where the mechanisms differ: the low
frequency regime, where the residual phase cannot resonate with a sum of two
primes, and the high frequency regime, where it can.  The assembly settles
modulus one by the parent's vanishing theorem and case splits the frequency.
-/
import LeanLab.Linnik1951.Decomp520a

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- LEAF. Low frequency regime. The mixed local contribution is at most the
scale N times the sixth power of the logarithm of N divided by the square root
of q times N to the one seventh, for every modulus from two up to N to the one
tenth and every residual frequency at most two.  In this range the residual
phase does not resonate with a sum of two primes inside the local window, so no
prime pair counting enters and the estimate is the easier half of the split. -/
theorem mixed_bound_small_frequency520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      2 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ 2 → n ≤ N →
      ‖mixedIntegral520 N q n‖ ≤ C * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. High frequency regime. The same bound for every residual frequency at
least three.  Here the residual phase does resonate with sums of two primes
inside the local window, so the prime pair count in a window of width q times N
to the one seventh enters; that counting is the harder half of the split. -/
theorem mixed_bound_large_frequency520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      2 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, 3 ≤ n → n ≤ N →
      ‖mixedIntegral520 N q n‖ ≤ C * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- The mixed estimate: at modulus one the mixed integral vanishes by the
parent's unit modulus theorem, so the bound is trivial there; from modulus two
on the two frequency leaves cover every residual frequency at most N, and the
larger of their two constants serves both. -/
theorem mixed_bound520_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖mixedIntegral520 N q n‖ ≤ C * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨C1, hC1, N1, h1⟩ := mixed_bound_small_frequency520 hG
  obtain ⟨C2, hC2, N2, h2⟩ := mixed_bound_large_frequency520 hG
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left C1 C2), max N1 N2, ?_⟩
  intro N hN q hq hqQ n hn
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left N1 N2) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right N1 N2) hN
  by_cases hq2 : 2 ≤ q
  · by_cases hn2 : n ≤ 2
    · refine (h1 N hN1 q hq2 hqQ n hn2 hn).trans ?_
      gcongr
      exact le_max_left C1 C2
    · have hn3 : 3 ≤ n := by omega
      refine (h2 N hN2 q hq2 hqQ n hn3 hn).trans ?_
      gcongr
      exact le_max_right C1 C2
  · have hqeq : q = 1 := by omega
    subst hqeq
    rw [mixed_unit520 N n, norm_zero]
    positivity

end LeanLab.Linnik1951
