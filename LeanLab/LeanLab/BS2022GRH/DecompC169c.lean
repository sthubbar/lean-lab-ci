/- AI wrote this Lean code for CODEX task169.
Lemma 7 with display 6, journal pp. 1219 to 1222. Goldbach is open. -/
import LeanLab.BS2022GRH.Lemma6Input138

namespace LeanLab.BS2022GRH.DecompC169c
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- The common prime Mertens constant M in Lemma 6, p. 1219 display 3.
The convergent prime series is the standard Meissel and Mertens constant. -/
def mertensConstant : ℝ := eulerMascheroniConstant +
  ∑' p : {p : ℕ // p.Prime}, (log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))

/-- LEAF. Small endpoint lower bound of Lemma 6, p. 1219 display 3.
Use Rosser and Schoenfeld Theorem 20 up to 10^8 and the paper computation to 10^12.
The finite computation and the treatment of the strict endpoint remain OPEN. -/
theorem reciprocal_lower_finite (x : ℝ) (hx : 3 ≤ x) (hx1 : x ≤ 1e12) :
    log (log x) + mertensConstant ≤
      ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
  sorry

/-- LEAF. Large endpoint lower bound of Lemma 6, p. 1219 display 3.
Use the explicit theta bound and the integral split at 10^19, pp. 1220 and 1221.
The two errors are 9.07982e-8 and 1.99551e-8. Their sum is 1.107533e-7. -/
theorem reciprocal_lower_infinite (x : ℝ) (hx : 1e12 < x) :
    log (log x) + mertensConstant - 1.107533e-7 ≤
      ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
  sorry

/-- LEAF. Upper bound of Lemma 6, p. 1219 display 3.
Use Broadbent et al. Table 15 and the partial summation identity 4, p. 1220.
The sum includes a prime at x, as required for the upper estimate. -/
theorem reciprocal_upper (x : ℝ) (hx : exp 2753 < x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) ≤
      log (log x) + mertensConstant + 2.28975e-9 / log x := by
  sorry

/-- Assemble the existing three-part Lemma6J with the same constant in every bound. -/
theorem lemma6J : Lemma6Input138.Lemma6J mertensConstant := by
  exact ⟨reciprocal_lower_finite, reciprocal_lower_infinite, reciprocal_upper⟩

/-- Exact existing Lemma7J with display 6.
Reuse all product, logarithm and square-tail proofs from task138. -/
theorem lemma7J : Lemma7J :=
  Lemma6Input138.lemma7J_of_lemma6 mertensConstant lemma6J

end
end LeanLab.BS2022GRH.DecompC169c

#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_lower_finite
#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_lower_infinite
#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_upper
#print axioms LeanLab.BS2022GRH.DecompC169c.lemma6J
#print axioms LeanLab.BS2022GRH.DecompC169c.lemma7J
