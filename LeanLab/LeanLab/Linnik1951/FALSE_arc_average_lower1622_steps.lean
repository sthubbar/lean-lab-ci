/-
FALSE_arc_average_lower1622_steps. AI wrote the Lean code. Binary Goldbach is open.

Split of the LEAF arc_average_lower1622 of FALSE_local_arc_shoulder1622_arc_mean_value.lean,
route burst 20261124 unit S7-05-x1. The LEAF there keeps its sorry until a follow-up; this
file proves the same statement as arc_average_lower1622_split from two pieces.

Step 1 of the route in the header of that file, the pairing, is proved here: a weighted
sum of localArc1622 N 1 n is the arc integral of the square of the damped prime series
against the trigonometric polynomial with those weights. It uses only linearity of the
interval integral and continuity of the series, continuous_prime_fourier111.

Steps 2 to 4, the choice of the Fejer weighted test polynomial, its circle energy and its
off arc tail, stay in one LEAF, arc_test_polynomial_lower1622, stated on the arc integral.
-/
import LeanLab.Linnik1951.FALSE_local_arc_shoulder1622_arc_mean_value
import LeanLab.Linnik1951.SecondMoment111

namespace LeanLab.Linnik1951.FALSEshoulder1622

open Filter LeanLab.Linnik1951
open scoped Topology

/-- Step 1, the pairing. A finite weighted sum of the modulus 1 arc integrals equals the
arc integral of the squared damped prime series against the weighted phases. -/
theorem arc_pairing1622 (N : ℕ) (hN : 1 ≤ N) (s : Finset ℤ) (h : ℤ → ℝ) :
    ∑ n ∈ s, ((h n : ℝ) : ℂ) * localArc1622 N 1 n =
      ∫ z in -(1 / (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        primeFourier111 N z ^ 2 *
          ∑ n ∈ s, ((h n : ℝ) : ℂ) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
  have hfilt : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  have hcont : ∀ n : ℤ, Continuous (fun z : ℝ => primeFourier111 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
    intro n
    exact ((continuous_prime_fourier111 N hN).pow 2).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
          continuous_const))
  unfold localArc1622
  rw [hfilt]
  simp only [Finset.sum_singleton, Nat.cast_zero, zero_div, zero_add]
  have step1 : ∀ n ∈ s, ((h n : ℝ) : ℂ) *
        (∫ z in -(1 / (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          primeFourier111 N z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ∫ z in -(1 / (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ((h n : ℝ) : ℂ) * (primeFourier111 N z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
    intro n _
    exact (intervalIntegral.integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl step1, ← intervalIntegral.integral_finsetSum]
  · refine intervalIntegral.integral_congr ?_
    intro z _
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n _
    ring
  · intro n _
    exact (continuous_const.mul (hcont n)).intervalIntegrable _ _

/-- LEAF: steps 2 to 4 of the refutation of the shoulder step of pages 159 to 161 at
modulus 1. Some nonnegative weights on integers at most N, of positive total, give a test
polynomial whose arc integral against the squared damped prime series has norm at least a
constant times the total weight times N over log^4 N. Route: Fejer weighted conjugate square
of the cut prime series; nonnegative circle energy by Chebyshev; Fejer tail off the arc by
Parseval. HARD. -/
theorem arc_test_polynomial_lower1622 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop, ∃ s : Finset ℤ, ∃ h : ℤ → ℝ,
      (∀ n ∈ s, n ≤ (N : ℤ) ∧ 0 ≤ h n) ∧ 0 < ∑ n ∈ s, h n ∧
        κ * (∑ n ∈ s, h n) * (N : ℝ) / Real.log N ^ 4 ≤
          ‖∫ z in -(1 / (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            primeFourier111 N z ^ 2 *
              ∑ n ∈ s, ((h n : ℝ) : ℂ) *
                Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ := by
  sorry

/-- The LEAF arc_average_lower1622, assembled from the pairing and the test polynomial
LEAF. Same statement as arc_average_lower1622. -/
theorem arc_average_lower1622_split :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop, ∃ s : Finset ℤ, ∃ h : ℤ → ℝ,
      (∀ n ∈ s, n ≤ (N : ℤ) ∧ 0 ≤ h n) ∧ 0 < ∑ n ∈ s, h n ∧
        κ * (∑ n ∈ s, h n) * (N : ℝ) / Real.log N ^ 4 ≤
          ‖∑ n ∈ s, ((h n : ℝ) : ℂ) * localArc1622 N 1 n‖ := by
  obtain ⟨κ, hκ, hev⟩ := arc_test_polynomial_lower1622
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  obtain ⟨s, h, hs, hpos, hge⟩ := hN
  refine ⟨s, h, hs, hpos, ?_⟩
  rw [arc_pairing1622 N hN1 s h]
  exact hge

end LeanLab.Linnik1951.FALSEshoulder1622

#print axioms LeanLab.Linnik1951.FALSEshoulder1622.arc_pairing1622
#print axioms LeanLab.Linnik1951.FALSEshoulder1622.arc_average_lower1622_split
