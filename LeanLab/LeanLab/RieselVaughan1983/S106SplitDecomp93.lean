import LeanLab.RieselVaughan1983.WeightedLower93
import LeanLab.RieselVaughan1983.S143SplitLemma3

/-! Split of the weighted lower leaf `Decomp93.weighted_lower`.
Riesel and Vaughan 1983, Ark. Mat. 21, page 53 Lemma 4 and page 54,
with the constant brackets of page 47 equations 2.20 to 2.22.
The assembly below has no sorry; it uses `WeightedLower93.weighted_lower_of`.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.S106SplitDecomp93
open Real
open Lemma4From393
noncomputable section

/-- Was LEAF, split by S143 in S143SplitLemma3: Lemma 3 on page 53, equation 3.14, the weighted sieve sum
approximation for every z at least 1. HARD for Codex. -/
theorem lemma3_eq314 : Lemma3.Lemma3ApproxP :=
  -- S143: split in S143SplitLemma3, three page 53 and display 2.14 leaves.
  LeanLab.RieselVaughan1983.S143SplitLemma3.lemma3_eq314_of_leaves

/-- Was LEAF, split by S143 in S143SplitBracketA6: page 47 equation 2.20, the lower bracket 8.463433 < A6 at lambda = 3/2.
Only the lower side is used. MEDIUM for Open Math OS. -/
theorem bracket_A6_lower : (8463433 / 1000000 : ℝ) ≤ A6 (3 / 2) :=
  -- S143: split in S143SplitBracketA6, from the display 2.14 lower bound of A3.
  LeanLab.RieselVaughan1983.S143SplitBracketA6.bracket_A6_lower_of_214

/-- LEAF: page 47 equation 2.21, the lower bracket -9.260623 < A7 at lambda = 3/2.
Only the lower side is used. MEDIUM for Open Math OS. -/
theorem bracket_A7_lower : -(9260623 / 1000000 : ℝ) ≤ A7 (3 / 2) := by
  sorry

/-- LEAF: page 47 equation 2.22, the upper bracket A8 < 9310.077 at lambda = 3/2.
Only the upper side is used. MEDIUM for Open Math OS. -/
theorem bracket_A8_upper : A8 (3 / 2) ≤ (9310077 / 1000 : ℝ) := by
  sorry

/-- LEAF: page 47 equation 2.22, the upper bracket A9 < 29.50889 at lambda = 3/2.
Only the upper side is used. MEDIUM for Open Math OS. -/
theorem bracket_A9_upper : A9 (3 / 2) ≤ (2950889 / 100000 : ℝ) := by
  sorry

/-- Assembly of `Decomp93.weighted_lower`, page 54, from the leaves above.
CONDITIONAL ON the five leaves. -/
theorem weighted_lower (x : ℝ) (hx : exp 24 ≤ x) :
    Decomp93.lowerPolynomial x < 8 * Ctw * Lemma3.S2 (sqrt (2 / 3 * x)) :=
  WeightedLower93.weighted_lower_of lemma3_eq314 bracket_A6_lower bracket_A7_lower
    bracket_A8_upper bracket_A9_upper x hx

end
end LeanLab.RieselVaughan1983.S106SplitDecomp93

#print axioms LeanLab.RieselVaughan1983.S106SplitDecomp93.weighted_lower
