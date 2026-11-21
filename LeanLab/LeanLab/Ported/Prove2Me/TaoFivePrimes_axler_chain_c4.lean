/-
Ported from Prove2Me, mission 0814790f.
Source TaoFivePrimes_axler_chain_c4. Author Nickrobbins95. Apache 2.0.
Lean 4.33.1 source adapted for Lean 4.35.0.
Derived certificates for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c4a
import LeanLab.Ported.Prove2Me.TaoFivePrimes_axler_chain_c4b
namespace LeanLab.Ported.Prove2Me.Task666


theorem TaoFivePrimes.axler_chain_c4 (hprev : (17382708166135 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (17387265 : ℝ) ≤ (17383459384328 : ℝ)) : ((52589385226535 : ℝ) ≤ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ∧ (1000000 : ℝ) * Chebyshev.theta (52597756 : ℝ) ≤ (52591511472754 : ℝ)) ∧ (∀ x : ℝ, (17387265 : ℝ) ≤ x → x < (52597756 : ℝ) → |Chebyshev.theta x - x| < 100 * x / (Real.log x) ^ 4) := by
  obtain ⟨b1, r1⟩ := TaoFivePrimes.axler_chain_c4a hprev
  obtain ⟨b2, r2⟩ := TaoFivePrimes.axler_chain_c4b b1
  refine ⟨b2, fun x hx1 hx2 => ?_⟩
  rcases lt_or_ge x (34129386 : ℝ) with h1 | h1
  · exact r1 x hx1 h1
  exact r2 x h1 hx2

end LeanLab.Ported.Prove2Me.Task666
