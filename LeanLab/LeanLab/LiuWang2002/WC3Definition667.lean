import LeanLab.LiuWang2002.WCDefinitions667

/-! The sealed Lemma 6.4 definition moved unchanged from Decomp1543c.
Source Liu and Wang page 169. AI wrote the Lean code. Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.U1543
open Real Finset ArithmeticFunction

/-- Lemma 6.4 p. 169, the statement of Wang-Chen 1994, Lemma 3: for `X ≥ 1`, `q ≥ 15`,
`∑_{n≤X} min(Y/n, 1/(2‖αn‖)) ≤ 5q + 1.5 q log q + X log q + 5Y q^(-1) log X`. -/
def WCLemma3 : Prop :=
  ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → 15 ≤ q → ∀ X Y : ℝ, 1 ≤ X → 0 < Y →
    ∑ n ∈ Icc 1 ⌊X⌋₊, minK (Y / n) (α * n) ≤
      5 * q + 1.5 * q * Real.log q + X * Real.log q + 5 * Y / q * Real.log X

end LeanLab.LiuWang2002.U1543
