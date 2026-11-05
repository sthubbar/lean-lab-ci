/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Separate the two prime summations in journal Lemma 14, pp. 1238 and 1239.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.MassInputs236

namespace LeanLab.BS2022GRH.Decomp374g
open Real Finset Classical ChenThresholdGRH SliceMass236
noncomputable section

/-- LEAF. Journal p. 1238, first apply Greaves Lemma 1 part ii and
Rosser and Schoenfeld Theorem 5 to the inner prime variable.
The short endpoint integral and the 27 over log cubed error are massErrorTail.
The remaining H prime sum is not yet estimated. -/
theorem inner_prime_sum (n : ℕ) (ε₁ : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1) :
    pairWeightSum n ε₁ ≤
      (∑ p ∈ U7153.Qset n, H n p / p) +
        (log (8 / 3) + 64 / log n ^ 2) * massErrorTail n ε₁ := by
  sorry

/-- LEAF. Journal pp. 1238 and 1239, the outer weighted prime summation.
Apply Greaves Lemma 1 part ii and Rosser and Schoenfeld Theorem 5 to H.
Use H at y equal to zero and H at z at most 0.56 over log N.
This estimate is independent of the slice width epsilon one. -/
theorem outer_prime_sum (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) :
    (∑ p ∈ U7153.Qset n, H n p / p) ≤
      (∫ u in U7153.zz n..U7153.yy n, H n u / (u * log u)) + 36 / log n ^ 3 := by
  sorry

/-- Exact statement of SliceMass236.pair_weight_mertens from the two separate prime steps.
CONDITIONAL ON inner_prime_sum and outer_prime_sum. No direct sorry. -/
theorem pair_weight_mertens (n : ℕ) (ε₁ : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1) :
    pairWeightSum n ε₁ ≤
      (∫ u in U7153.zz n..U7153.yy n, H n u / (u * log u)) + 36 / log n ^ 3 +
        (log (8 / 3) + 64 / log n ^ 2) * massErrorTail n ε₁ := by
  linarith only [inner_prime_sum n ε₁ hn hε hε1, outer_prime_sum n hn]

end
end LeanLab.BS2022GRH.Decomp374g

#print axioms LeanLab.BS2022GRH.Decomp374g.inner_prime_sum
#print axioms LeanLab.BS2022GRH.Decomp374g.outer_prime_sum
#print axioms LeanLab.BS2022GRH.Decomp374g.pair_weight_mertens
