/-
Jia 1996, Lemma 28, pages 285 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Two proper region estimates remain OPEN. The final assembly is CONDITIONAL.
The sealed group5_lower is unchanged.
-/
import LeanLab.Languasco2004.GroupSplit548

namespace LeanLab.Languasco2004.Decomp548e
open Finset Real Decomp279a Decomp316c GroupSplit548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Jia page 285, Lemma 28, supporting display 65 on page 286.
Only region 1 of group 5 is bounded. The coefficient is 0.468045.
The finite caps, strict endpoints and recovery clipping remain explicit. -/
theorem region1_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 5 1 true N (localization N ε) n <
        0.468045 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia page 285, Lemma 28, supporting display 65 on page 286.
Only group 5 with region 1 removed is bounded. The coefficient is 0.542578.
This is a proper subfamily of the parent group. Endpoint conventions stay sealed. -/
theorem remainder_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 5 1 false N (localization N ε) n <
        0.542578 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Jia Lemma 28: the exact sealed group5_lower statement follows
from the two smaller region estimates. CONDITIONAL ON region1_lower
and remainder_lower. There is no admission in this assembly. -/
theorem group5_lower_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => groupSum 5 N (localization N ε) n <
        1.010623 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e1, he1, h1⟩ := region1_lower
  obtain ⟨e2, he2, h2⟩ := remainder_lower
  refine ⟨min e1 e2, lt_min he1 he2, ?_⟩
  intro ε B hε he hB
  obtain ⟨C1, N1, hC1⟩ := h1 ε B hε (he.trans_le (min_le_left _ _)) hB
  obtain ⟨C2, N2, hC2⟩ := h2 ε B hε (he.trans_le (min_le_right _ _)) hB
  refine ⟨C1 + C2, max N1 N2, ?_⟩
  intro N hN
  have hb := combine_counts (window N ε)
    (pieceSum 5 1 true N (localization N ε))
    (pieceSum 5 1 false N (localization N ε))
    (groupSum 5 N (localization N ε)) (scale N (localization N ε))
    0.468045 0.542578 1.010623
    (C1 * windowLength N ε / Real.log N ^ B)
    (C2 * windowLength N ε / Real.log N ^ B)
    (by norm_num) (pieceSum_add 5 1 N (localization N ε))
    (hC1 N ((le_max_left _ _).trans hN))
    (hC2 N ((le_max_right _ _).trans hN))
  convert hb using 1 <;> ring

#print axioms region1_lower
#print axioms remainder_lower
#print axioms group5_lower_from_parts
end
end LeanLab.Languasco2004.Decomp548e
