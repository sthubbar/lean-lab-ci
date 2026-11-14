/-
Jia 1996, Lemma 25, pages 275 to 277.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Two proper region estimates remain OPEN. The final assembly is CONDITIONAL.
The sealed group2_lower is unchanged.
-/
import LeanLab.Languasco2004.GroupSplit548

namespace LeanLab.Languasco2004.Decomp548b
open Finset Real Decomp279a Decomp316c GroupSplit548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Jia page 275, Lemma 25, supporting display 65 on page 286.
Only region 47 of group 2 is bounded. The coefficient is 0.005888.
The finite caps, strict endpoints and recovery clipping remain explicit. -/
theorem region47_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 2 47 true N (localization N ε) n <
        0.005888 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia page 277, Lemma 25, supporting display 65 on page 286.
Only group 2 with region 47 removed is bounded. The coefficient is 0.341293.
This is a proper subfamily of the parent group. Endpoint conventions stay sealed. -/
theorem remainder_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 2 47 false N (localization N ε) n <
        0.341293 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Jia Lemma 25: the exact sealed group2_lower statement follows
from the two smaller region estimates. CONDITIONAL ON region47_lower
and remainder_lower. There is no admission in this assembly. -/
theorem group2_lower_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => groupSum 2 N (localization N ε) n <
        0.347181 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e1, he1, h1⟩ := region47_lower
  obtain ⟨e2, he2, h2⟩ := remainder_lower
  refine ⟨min e1 e2, lt_min he1 he2, ?_⟩
  intro ε B hε he hB
  obtain ⟨C1, N1, hC1⟩ := h1 ε B hε (he.trans_le (min_le_left _ _)) hB
  obtain ⟨C2, N2, hC2⟩ := h2 ε B hε (he.trans_le (min_le_right _ _)) hB
  refine ⟨C1 + C2, max N1 N2, ?_⟩
  intro N hN
  have hb := combine_counts (window N ε)
    (pieceSum 2 47 true N (localization N ε))
    (pieceSum 2 47 false N (localization N ε))
    (groupSum 2 N (localization N ε)) (scale N (localization N ε))
    0.005888 0.341293 0.347181
    (C1 * windowLength N ε / Real.log N ^ B)
    (C2 * windowLength N ε / Real.log N ^ B)
    (by norm_num) (pieceSum_add 2 47 N (localization N ε))
    (hC1 N ((le_max_left _ _).trans hN))
    (hC2 N ((le_max_right _ _).trans hN))
  convert hb using 1 <;> ring

#print axioms region47_lower
#print axioms remainder_lower
#print axioms group2_lower_from_parts
end
end LeanLab.Languasco2004.Decomp548b
