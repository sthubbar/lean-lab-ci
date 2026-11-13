/-
The two cases of the window count of P0039 L. Grimmelt and J. Teravainen, arXiv 2508.16400v2,
pages 67 and 69, kept in their own module so that the split module
`LeanLab.ExceptionalSet.SPLIT_grimmeltTeravainen` itself carries no admission. That module states
the two cases and proves each of them from the matching declaration below, by name, and its
assembly of the two into `GT11` is closed.

Both declarations are OPEN, each with its own case hypothesis, and neither of them is `GT11`.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.GrimmeltTeravainen2025Sorting

open Finset
open LeanLab.AlmostPrimes

namespace LeanLab.ExceptionalSet

open LeanLab.ExceptionalSet.GT2025

attribute [local instance] Classical.propDecidable

/-- LEAF: page 67 of P0039, the unexceptional case of the window count, Lemma 8.3 with the upper
bound sieve. For the saving `δ₁ ^ 6` and every `N` from some point on at which no primitive
Dirichlet character of modulus at most `N ^ (2 * δ₁ ^ 3)` has a real zero above
`1 - (1 / 2) / log (N ^ (2 * δ₁ ^ 3))`, the `m ≡ 4 mod 6` of the window `[5N/4, 7N/4]` that are
not a sum of two Chen primes number at most a constant times `N ^ (1 - δ₁ ^ 6) * log N`. The
logarithmic loss and the smaller saving make it weaker than the page. -/
theorem window_count_unexceptional_case :
    ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 / 200 → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ¬ (∃ (r : ℕ) (χ : DirichletCharacter ℂ (r + 1)) (β : ℝ),
          3 ≤ r + 1 ∧ (r + 1 : ℝ) ≤ (N : ℝ) ^ (2 * δ₁ ^ 3) ∧ χ.IsPrimitive ∧ χ ≠ 1 ∧
            β < 1 ∧ 1 - (1 / 2) / Real.log ((N : ℝ) ^ (2 * δ₁ ^ 3)) ≤ β ∧
              DirichletCharacter.LFunction χ (β : ℂ) = 0) →
        (cntI ChenBad N : ℝ) ≤ C * (N : ℝ) ^ (1 - δ₁ ^ 6) * Real.log (N : ℝ) := by
  sorry

/-- LEAF: page 69 of P0039, the exceptional case of the window count, Lemma 8.4 and the partition
of the window by `σ₁(m)` at `-1 / 2`. The same count at the same saving and with the same
logarithmic loss, at the `N` for which some primitive Dirichlet character of modulus at most
`N ^ (2 * δ₁ ^ 3)` has a real zero above `1 - (1 / 2) / log (N ^ (2 * δ₁ ^ 3))`. That hypothesis
is the extra input of this case. -/
theorem window_count_exceptional_case :
    ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 / 200 → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∃ (r : ℕ) (χ : DirichletCharacter ℂ (r + 1)) (β : ℝ),
          3 ≤ r + 1 ∧ (r + 1 : ℝ) ≤ (N : ℝ) ^ (2 * δ₁ ^ 3) ∧ χ.IsPrimitive ∧ χ ≠ 1 ∧
            β < 1 ∧ 1 - (1 / 2) / Real.log ((N : ℝ) ^ (2 * δ₁ ^ 3)) ≤ β ∧
              DirichletCharacter.LFunction χ (β : ℂ) = 0) →
        (cntI ChenBad N : ℝ) ≤ C * (N : ℝ) ^ (1 - δ₁ ^ 6) * Real.log (N : ℝ) := by
  sorry

end LeanLab.ExceptionalSet
