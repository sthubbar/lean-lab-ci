/-
The existing qualitative zero free region definition from State1535.
Davenport, Multiplicative Number Theory, chapter 14.
The declaration is moved verbatim to remove an import cycle.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Ternary.U1535

/-- A zero-free region away from the real axis: for every modulus `q ≥ 1`, every Dirichlet
character `χ` mod `q`, and `s = σ + it` with `|t| ≥ 1` and
`σ ≥ 1 - 1 / (c log (q (|t| + 2)))`, `L(s, χ) ≠ 0`. -/
def ZeroFreeHigh (c : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ), 1 ≤ |t| →
    1 - 1 / (c * Real.log (q * (|t| + 2))) ≤ σ →
      DirichletCharacter.LFunction χ (σ + t * Complex.I) ≠ 0


end LeanLab.Ternary.U1535
