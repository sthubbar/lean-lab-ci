import Mathlib

/-
AI wrote this Lean code. Binary Goldbach is open.
Decomposition of P0099 Lemma 1 from page 14.
P0099 is Ramare and Saouter, Short effective intervals containing primes, 2003.
-/

namespace LeanLab.Ternary78.Paper104

/-- CITED. P0099 page 14 Lemma 1. -/
def Lemma1 (N : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 10^3 ≤ T →
    |N T - (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)|
    ≤ 0.67 * Real.log (T / (2 * Real.pi))

/-- LEAF. P0099 page 14 Lemma 1 relies on Theorem 19 of Rosser (reference [21] in P0099, actually Rosser 1941, "Explicit bounds for some functions of prime numbers"). -/
theorem lemma1_rosser_thm19 (N : ℝ → ℝ) (T : ℝ) (hT : 10^3 ≤ T) :
  |N T - (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)|
    ≤ 0.67 * Real.log (T / (2 * Real.pi)) := by
  sorry

/-- The exact cited Lemma1 Prop, assembled from its paper proof leaves. -/
theorem lemma1_decomposed (N : ℝ → ℝ) : Lemma1 N := by
  intro T hT
  exact lemma1_rosser_thm19 N T hT

end LeanLab.Ternary78.Paper104
