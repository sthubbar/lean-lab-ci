/-
Ported from Prove2Me, mission 0814790f.
Source TaoFivePrimes_axler_chain_c5a. Author Nickrobbins95. Apache 2.0.
Lean 4.33.1 source adapted for Lean 4.35.0.
Derived certificates for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c5a1
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c5a2
namespace LeanLab.Ported.Prove2Me.Task666


theorem TaoFivePrimes.axler_chain_c5a (hprev : (52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) : ((69344896246415 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (69355435 : ℝ) ≤ (69347654882929 : ℝ)) ∧ (∀ x : ℝ, (52597756 : ℝ) ≤ x → x < (69355435 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  obtain ⟨b1, r1⟩ := TaoFivePrimes.axler_chain_c5a1 hprev
  obtain ⟨b2, r2⟩ := TaoFivePrimes.axler_chain_c5a2 b1
  refine ⟨b2, fun x hx1 hx2 => ?_⟩
  rcases lt_or_ge x (60984648 : ℝ) with h1 | h1
  · exact r1 x hx1 h1
  exact r2 x h1 hx2

end LeanLab.Ported.Prove2Me.Task666
