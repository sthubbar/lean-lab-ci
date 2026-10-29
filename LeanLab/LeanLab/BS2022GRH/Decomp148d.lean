/- AI wrote this Lean code for CODEX task148.
Recovered from the recorded write commands. Fresh checks are required.
Journal Lemma 8, normalization and exact assembly. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC164b
import LeanLab.BS2022GRH.Decomp148c
namespace LeanLab.BS2022GRH.Decomp148d
open Real Finset Classical ChenThresholdGRH Decomp148a Decomp148b Decomp148c
/-- LEAF. Normalize display 13 to display 17, p. 1226.
Substitute the cube root cutoff. The rounding 1.3841 / 2 = 0.69205 is exact. -/
theorem small_normalized (X Y D : ℝ) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hD : 1 < D) (hDX : D < √(X * Y))
    (hbal : √(X * Y) / D ≤ cutoff Y) (hcutD : cutoff Y ≤ D) :
    smallBound X Y D (cutoff Y) ≤ smallCoeff X Y D * scale X Y D := by
  exact (DecompC164b.small_identity X Y D hX hY hD hDX hbal hcutD).le
/-- LEAF. Normalize display 16 to display 18, p. 1226.
Simplify real powers and the reciprocal cutoff term. -/
theorem large_normalized (X Y D : ℝ) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hD : 1 < D) (hDX : D < √(X * Y))
    (hbal : √(X * Y) / D ≤ cutoff Y) (hcutD : cutoff Y ≤ D) :
    largeBound X Y D (cutoff Y) ≤ largeCoeff X Y D * scale X Y D := by
  exact (DecompC164b.large_identity X Y D hX hY hD hDX hbal hcutD).le
/-- Elementary strict cutoff range from the balancing condition, p. 1226. -/
theorem cutoff_gt_one (X Y D : ℝ) (hD : 1 < D) (hDX : D < √(X * Y))
    (hbal : √(X * Y) / D ≤ cutoff Y) : 1 < cutoff Y := by
  exact lt_of_lt_of_le ((one_lt_div (by linarith : 0 < D)).2 hDX) hbal
/-- Exact Lemma8J assembly. OPEN through its named leaves, with no direct sorry. -/
theorem lemma8J : Lemma8J := by
  intro hG c X Y Z D a hc hX hY hZ hZY hD hDX hbal hcutD ha
  have hcut := cutoff_gt_one X Y D hD hDX hbal
  have hs := (small_at_cutoff hG c X Y Z D a hc hX hY hZ hZY hD hcut hcutD hbal ha).trans
    (small_normalized X Y D hX hY hD hDX hbal (hcutD.trans (min_le_left _ _)))
  have hl := (large_at_cutoff c X Y Z D a hc hX hY hZ hZY hD hDX hcut hcutD hbal ha).trans
    (large_normalized X Y D hX hY hD hDX hbal (hcutD.trans (min_le_left _ _)))
  calc bilinear c X Y Z D a
      ≤ smallMass c X Y Z D (cutoff Y) a + largeMass c X Y Z D (cutoff Y) a :=
        split_reduction c X Y Z D (cutoff Y) a hD ha
    _ ≤ smallCoeff X Y D * scale X Y D + largeCoeff X Y D * scale X Y D := add_le_add hs hl
    _ = mJ X Y D * scale X Y D := by rw [mJ, add_mul]
end LeanLab.BS2022GRH.Decomp148d
#print axioms LeanLab.BS2022GRH.Decomp148d.small_normalized
#print axioms LeanLab.BS2022GRH.Decomp148d.large_normalized
#print axioms LeanLab.BS2022GRH.Decomp148d.cutoff_gt_one
#print axioms LeanLab.BS2022GRH.Decomp148d.lemma8J
