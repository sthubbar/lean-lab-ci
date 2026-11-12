/-
Gallagher 1975 P0094 pp.131 and 132 displays 15 to 17, the positive exceptional
conductor case of the major arc reduction.
CONDITIONAL ON the leaves in Leaves13.lean and Leaves1517.lean.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.MajorArcEnergy.Display13
import LeanLab.Linnik.MajorArcEnergy.Leaves1517

namespace LeanLab.Linnik.MajorArcEnergy

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries ramanujanSum excSet)
open LeanLab.Linnik.U7204 (Sg)

/-- CONDITIONAL ON `major_arc_pair_expansion`, `pair_weight_bound`, `principal_pair_sum`
and `exceptional_weight_bound`. Gallagher 1975 pp.131 and 132 displays 15 to 17: with the
exceptional character chi~ to conductor r, the pairs avoiding chi~ are treated as in
display 13, display 15 bounds the pairs of chi~ with chi not 1 or chi~, and displays 16 and
17 bound the remaining pairs by N L^(-2) n/phi(n) r phi((n, r))/phi(r)^2.
The statement is exactly that of `Decomp486b.major_arc_energy_exceptional`. -/
theorem major_arc_energy_exceptional_split
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by
  sorry

end LeanLab.Linnik.MajorArcEnergy
