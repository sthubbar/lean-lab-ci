/- AI wrote the Lean code for CODEX task236.
Published input for the Theorem 7 slice sieve. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169a

namespace LeanLab.BS2022GRH.PublishedInputs236
open Real Finset ChenThresholdGRH DecompC169a

/-- LEAF. The upper product estimate in journal Lemma 10, p. 1227,
applied at y in the proof of display 29, p. 1236.
CITED from Nathanson Theorem 10.3 and Schoenfeld Corollary 3.
UNfull uses the lab normalization, which makes this upper bound weaker. -/
theorem density_y_upper (n : ℕ) (hG : GRH) (hn : exp (exp 10) ≤ (n : ℝ)) (hev : Even n) :
    (∏ p ∈ primesBelow n (U7153.yy n), (1 - 1 / ((p : ℝ) - 1))) ≤
      3 * UNfull n / log n * (1 + 0.06 * log n / (n : ℝ) ^ (1 / 6 : ℝ)) := by
  sorry

end LeanLab.BS2022GRH.PublishedInputs236
#print axioms LeanLab.BS2022GRH.PublishedInputs236.density_y_upper
