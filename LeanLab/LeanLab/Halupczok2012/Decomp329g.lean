import LeanLab.Halupczok2012.Decomp329f
import LeanLab.Halupczok2012.Decomp329b

/-!
Fixed exponent analytic supply for the sealed Wu leaf.
Source: Halupczok page 345 and Wu arXiv 0705.1652 pages 5, 34, 38 and 42.
The sole new open leaf concerns only windows of length X to 0.971.
The restriction at 3 comes from the rough sieve support in the written weight proof.
The unrestricted statement of Theorem 5 alone does not give that restriction.
The weight parameter adaptation remains a recorded QUESTION.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp329g

open scoped Classical

/-- LEAF. Halupczok page 345, Wu arXiv page 5 Theorem 5 at theta 0.971.
Use the rough sieved contribution in the proof on pages 34, 38 and 42.
Only the one power length X to 0.971 is counted, with denominator log X squared.
The full range in Y and its logarithm conversion are proved in Decomp329f.
The restricted rough count and the printed parameter adaptation are not formalized here. -/
theorem fixed_wu_rough_count_leaf :
    ∃ c > 0, ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → 2 ≤ X →
      c * X ^ (0.971 : ℝ) / (Real.log X) ^ 2 ≤
        (((kRange X (X ^ (0.971 : ℝ))).filter
          (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card : ℝ) := by
  sorry

/-- Halupczok page 345, the exact sealed Wu statement from the fixed exponent leaf.
This assembly has no sorry of its own and remains conditional on that open leaf. -/
theorem wu_supply :
  ∃ c > 0, ∃ Y0 > 0, ∀ (X Y : ℝ), Y0 ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
    c * Y / (Real.log Y) ^ 2 ≤ (@Finset.filter ℕ (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2)) (Classical.decPred _) (kRange X Y)).card := Decomp329f.wu_of_fixed_power_count fixed_wu_rough_count_leaf

/-- Halupczok pages 345 to 346, the exact sealed assembly statement.
Only Corollary2 and the fixed exponent leaf are inputs to this supply. -/
theorem corollary_3_supply (hCor2 : Corollary2) : Corollary3 :=
  Decomp329b.corollary3_of_inputs hCor2 wu_supply

end LeanLab.Halupczok2012.Decomp329g
