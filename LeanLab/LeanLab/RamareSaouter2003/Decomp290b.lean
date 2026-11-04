import LeanLab.RamareSaouter2003.Lemma1Zeta
import LeanLab.RamareSaouter2003.VerifyU1333Rosser

/-!
P0099, Lemma 1, printed p. 14, citing Rosser 1941, Theorem 19, p. 223.
The scalar error comparison is already proved in VerifyU1333Rosser.
AI wrote this Lean code. Binary Goldbach is OPEN.
The counting input is OPEN. All conclusions here are CONDITIONAL ON it.
-/

namespace LeanLab.RamareSaouter2003.Decomp290b

open Real Row1

/-- LEAF. P0099 p. 14, Lemma 1 proof, citing Rosser 1941, Theorems 17
and 18, p. 223. On this finite height range Rosser gives the stronger error
bound 2. The upper endpoint 1400 is below his cutoff A = 1467.47747.... -/
theorem low_count (T : ℝ) (hT : 1000 ≤ T) (hThi : T ≤ 1400) :
    |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤ 2 := by
  sorry

/-- LEAF. P0099 p. 14, Lemma 1 proof, citing Rosser 1941, Theorem 19,
pp. 223 and 224. This is only the high range of Rosser's original bound.
The proof uses Backlund's method above Rosser's cutoff A. -/
theorem high_count (T : ℝ) (hT : 1400 ≤ T) :
    |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 := by
  sorry

/-- Lemma 1 with both signs, P0099 p. 14. CONDITIONAL ON low_count and high_count.
The 0.2/T slack in the existing scalar comparison is nonnegative. -/
theorem lemma1_two_sided : L1Zeta.Lemma1N := by
  intro T hT
  by_cases h : T ≤ 1400
  · have hR := low_count T hT h
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1000) hT
    have hlow := VerifyU1333.log_thousand_ge
    have hpi := VerifyU1333.log_two_pi_le
    have hbound : (2 : ℝ) ≤ 0.67 * Real.log (T / (2 * π)) := by
      rw [Real.log_div (by linarith : T ≠ 0) (by positivity : 2 * π ≠ 0)]
      linarith
    exact hR.trans hbound
  · have hR := high_count T (by linarith)
    have hE := VerifyU1333.rosser_err_le T hT
    have hpos : 0 ≤ (0.2 : ℝ) / T := div_nonneg (by norm_num) (by linarith)
    linarith

/-- The exact statement of Decomp126.lemma1_cited, P0099 p. 14.
CONDITIONAL ON low_count and high_count. No sorry occurs in this assembly. -/
theorem lemma1_cited : Lemma1Upper L1Zeta.NZr := by
  intro T hT
  have h := lemma1_two_sided T hT
  have hab := le_abs_self (L1Zeta.NZr T -
    (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8))
  linarith

end LeanLab.RamareSaouter2003.Decomp290b

#print axioms LeanLab.RamareSaouter2003.Decomp290b.low_count
#print axioms LeanLab.RamareSaouter2003.Decomp290b.high_count
#print axioms LeanLab.RamareSaouter2003.Decomp290b.lemma1_two_sided
#print axioms LeanLab.RamareSaouter2003.Decomp290b.lemma1_cited
