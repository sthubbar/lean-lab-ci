/-
Split of the conductor zero major arc frequency estimate.
The frequency error is the norm of the difference of the arc integral and the main
term, so the estimate follows from a bound on each of the two summands separately.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp486b

namespace LeanLab.Linnik.Decomp486b

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries)
open LeanLab.Linnik.U7204 (Sg)

/-- LEAF. Step one of the triangle inequality: the major arc integral of the squared
generating function against the character exponential, taken in norm, is at most the
constant times the scale N over log squared N, the totient weight of the frequency,
and the sum of the divisor count term and the corrected energy term, the energy being
the conductor zero normalized energy. -/
theorem leaf_arc_integral_part_bound :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 →
          ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
                LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := by
  sorry

/-- LEAF. Step two of the triangle inequality: the product of the correlation count
with the singular series, taken in norm, is at most the constant times the same scale
N over log squared N, the totient weight of the frequency, and the sum of the divisor
count term and the conductor zero corrected energy term. -/
theorem leaf_main_series_part_bound :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 →
          ‖(Jn N n : ℂ) * singSeries n‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := by
  sorry

/-- The conductor zero frequency estimate follows from the two summand bounds.
Combine the two bounds with the triangle inequality, add the constants and take the
smaller of the two exponent thresholds. -/
theorem major_arc_energy_zero_split
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
          K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
            (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
              (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0)
:= by
  obtain ⟨K₁, θ₁, hK₁, hθ₁, hθ₁', hz₁⟩ := leaf_arc_integral_part_bound
  obtain ⟨K₂, θ₂, hK₂, hθ₂, hθ₂', hz₂⟩ := leaf_main_series_part_bound
  refine ⟨K₁ + K₂, min θ₁ θ₂, by linarith, lt_min hθ₁ hθ₂,
    (min_le_left _ _).trans hθ₁', ?_⟩
  intro θ hθ hθm
  obtain ⟨N₁, hN₁⟩ := hz₁ θ hθ (hθm.trans (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hz₂ θ hθ (hθm.trans (min_le_right _ _))
  refine ⟨max 2 (max N₁ N₂), ?_⟩
  intro N hN n hn
  have hN1 : N₁ ≤ N := (le_max_left N₁ N₂).trans ((le_max_right 2 _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right N₁ N₂).trans ((le_max_right 2 _).trans hN)
  have hsplit : complexFrequencyError N θ n ≤
      ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
          ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ +
        ‖(Jn N n : ℂ) * singSeries n‖ := by
    unfold complexFrequencyError
    exact norm_sub_le _ _
  have hI := hN₁ N hN1 n hn
  have hT := hN₂ N hN2 n hn
  calc complexFrequencyError N θ n ≤
      ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
          ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ +
        ‖(Jn N n : ℂ) * singSeries n‖ := hsplit
    _ ≤ K₁ * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) +
        K₂ * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := add_le_add hI hT
    _ = (K₁ + K₂) * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := by
      ring

end LeanLab.Linnik.Decomp486b

open LeanLab.Linnik.Decomp486b in
#print axioms major_arc_energy_zero_split
