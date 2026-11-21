import Mathlib

/-!
Shared sealed definitions for the Wang and Chen estimates on Liu and Wang page 169.
These declarations moved unchanged from Decomp1543a.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.U1543
open Real Finset ArithmeticFunction

/-- `‖x‖`, the distance from `x` to the nearest integer, Lemma 6.3 p. 169. -/
noncomputable def nint (x : ℝ) : ℝ := |x - round x|

/-- `min(X, 1/(2‖θ‖))`, read as `X` when `θ` is an integer. -/
noncomputable def minK (X θ : ℝ) : ℝ := if nint θ = 0 then X else min X (1 / (2 * nint θ))

/-- (6.1) p. 168: `α = a/q + θ/q^2` with `q ≥ 1`, `(a, q) = 1`, `|θ| ≤ 1`. -/
def Dioph (α : ℝ) (a : ℤ) (q : ℕ) : Prop :=
  1 ≤ q ∧ Int.gcd a q = 1 ∧ |α - a / q| ≤ 1 / (q : ℝ) ^ 2

/-- Lemma 6.3 p. 169, the statement of Wang-Chen 1994, Lemma 2. -/
def WCLemma2 : Prop :=
  ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → ∀ X : ℝ, 0 < X → ∀ (Y : ℕ) (Z : ℤ), 1 ≤ Y →
    ∑ n ∈ Ioc Z (Z + Y), minK X (α * n) ≤ (((Y / q : ℕ) : ℝ) + 1) * (5 * X + q * Real.log q)

end LeanLab.LiuWang2002.U1543
