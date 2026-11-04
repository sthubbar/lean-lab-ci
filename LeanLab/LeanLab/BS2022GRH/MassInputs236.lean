/- AI wrote the Lean code for CODEX task236.
Weighted Mertens input for journal Lemma 14. Goldbach is open. -/
import LeanLab.BS2022GRH.OuterIntegral236
namespace LeanLab.BS2022GRH.SliceMass236
open Real Finset Classical
noncomputable section

/-- The short interval and endpoint errors, journal p. 1238. -/
def massErrorTail (n : ℕ) (ε₁ : ℝ) : ℝ :=
  log √(1 + ε₁) / (log (U7153.yy n) ^ 2 - log √(1 + ε₁) ^ 2) + 27 / log n ^ 3

/-- LEAF. Quantitative weighted prime summation error, journal pp. 1238 and 1239.
CITED inputs are reference 7 Lemma 1 part ii and reference 17 Theorem 5.
The main integral is kept explicit. Its exact evaluation is proved in OuterIntegral236.
The finite triple reduction and Schoenfeld count are not part of this input. -/
theorem pair_weight_mertens (n : ℕ) (ε₁ : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1) :
    pairWeightSum n ε₁ ≤
      (∫ u in U7153.zz n..U7153.yy n, H n u / (u * log u)) + 36 / log n ^ 3 +
        (log (8 / 3) + 64 / log n ^ 2) * massErrorTail n ε₁ := by
  sorry

end
end LeanLab.BS2022GRH.SliceMass236
#print axioms LeanLab.BS2022GRH.SliceMass236.pair_weight_mertens
