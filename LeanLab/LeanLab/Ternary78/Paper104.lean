import Mathlib

/-
AI wrote this Lean code. Binary Goldbach is open.
P0099 is Ramare and Saouter, Short effective intervals containing primes, 2003.
Source: https://doi.org/10.1016/S0022-314X(02)00029-X
This records its main theorem as requested by task104. No analytic input is proved here.
-/

namespace LeanLab.Ternary78.Paper104

/-- CITED. P0099 printed page 13, Theorem 3, with its strict lower endpoint.
The threshold is strict as printed in the theorem. -/
def PrimeInterval : Prop :=
  ∀ x : ℝ, 10726905041 < x →
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < (p : ℝ) ∧ (p : ℝ) ≤ x

/-- CITED. P0099 printed page 22, Lemma 7.
The positive integer m and nonnegative u are inherited from the surrounding argument. -/
def Lemma7 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (u a : ℝ), 0 ≤ u → 0 ≤ a → a ≤ 1 / 2 →
    1 - (1 + m * u * a) / (1 + m * u * (1 - a)) * Real.exp (-u) ≤
      u * (1 + (1 - 2 * a) * m)

end LeanLab.Ternary78.Paper104
