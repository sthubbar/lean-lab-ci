/-
Jia 1996, Lemma 26, pages 279 to 280.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Two proper region estimates remain OPEN. The final assembly is CONDITIONAL.
The sealed group3_lower is unchanged.
-/
import LeanLab.Languasco2004.GroupSplit548

namespace LeanLab.Languasco2004.Decomp548c
open Finset Real Decomp279a Decomp316c GroupSplit548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Jia page 279, Lemma 26, supporting display 65 on page 286.
Only region 4 of group 3 is bounded. The coefficient is 0.009636.
The finite caps, strict endpoints and recovery clipping remain explicit. -/
theorem region4_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 3 4 true N (localization N ε) n <
        0.009636 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  -- BLOCKED 2026-11-15 FREE-ms-leanstral task520 region4_lower
  -- OUT OF REACH: requires Jia 1996 Lemma 26 display 65, the large-sieve/Gallagher
  -- estimate bounding |{n ∈ window : pieceSum 3 4 true < 0.009636 * scale}| = O(windowLength / log^B N).
  -- No CITED lemma in Decomp279a, Decomp316c, or GroupSplit548 provides this.
  -- All 5 group_lower lemmas in Decomp316c are sorried; Decomp279a's initial_bound,
  -- subtraction_bound, recovery_bound are sorried.
  -- The analytic core is research-level formalization of exponential sum bounds.
  -- Searched all imported files: no CITED region-level count bound found.
  sorry

/-- LEAF. Jia page 280, Lemma 26, supporting display 65 on page 286.
Only group 3 with region 4 removed is bounded. The coefficient is 0.289310.
This is a proper subfamily of the parent group. Endpoint conventions stay sealed. -/
theorem remainder_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 3 4 false N (localization N ε) n <
        0.289310 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  -- BLOCKED 2026-11-22 FREE-nv-glm5 task2583 remainder_lower
  -- OUT OF REACH. Attempted 2026-11-22 the only elementary route (Finset.filter_subset
  -- + Finset.card_le_card). Own lake build error at the final exact_mod_cast:
  --   mod_cast has type #(filter ... pieceSum 3 4 false ... < 0.289310 * scale ...) ≤
  --     #(window N ε)
  --   but is expected to have type
  --     ↑(#(filter ...)) ≤ 1 * windowLength N ε / log N ^ B
  -- i.e. only card ≤ card (window N ε) is available, and card (window N ε) is not
  -- ≤ C * windowLength N ε / Real.log N ^ B for fixed C since Real.log N ^ B → ∞.
  -- Missing result: Jia 1996 Lemma 26 display 65 (p. 286) large-sieve/Gallagher
  -- small-value bound #{n ∈ window : pieceSum 3 4 false < 0.289310 * scale}
  -- = O(windowLength N ε / log^B N). Searches run 2026-11-22: LeanSearch
  -- "exceptional set estimate large sieve ... window length over log power" and
  -- "large sieve inequality sum over moduli exponential sum mean value bound"
  -- returned only Mathlib SelbergSieve/BoundingSieve (combinatorial sifted-set
  -- bounds, no exceptional-set count bound); Loogle (Finset.filter _ _).card ≤
  -- _ / Real.log _ ^ _ returned count 0; Loogle Gallagher large sieve Real.log
  -- returned unknown identifier. Grep of Decomp279a/Decomp316c/GroupSplit548/
  -- Decomp316a/Geometry316/StatementsA found no card/log^B count bound except
  -- extend_windows, which takes such a bound as hypothesis. Not in Mathlib, not
  -- CITED in any imported lab file.
  sorry

/-- Jia Lemma 26: the exact sealed group3_lower statement follows
from the two smaller region estimates. CONDITIONAL ON region4_lower
and remainder_lower. There is no admission in this assembly. -/
theorem group3_lower_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => groupSum 3 N (localization N ε) n <
        0.298946 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e1, he1, h1⟩ := region4_lower
  obtain ⟨e2, he2, h2⟩ := remainder_lower
  refine ⟨min e1 e2, lt_min he1 he2, ?_⟩
  intro ε B hε he hB
  obtain ⟨C1, N1, hC1⟩ := h1 ε B hε (he.trans_le (min_le_left _ _)) hB
  obtain ⟨C2, N2, hC2⟩ := h2 ε B hε (he.trans_le (min_le_right _ _)) hB
  refine ⟨C1 + C2, max N1 N2, ?_⟩
  intro N hN
  have hb := combine_counts (window N ε)
    (pieceSum 3 4 true N (localization N ε))
    (pieceSum 3 4 false N (localization N ε))
    (groupSum 3 N (localization N ε)) (scale N (localization N ε))
    0.009636 0.289310 0.298946
    (C1 * windowLength N ε / Real.log N ^ B)
    (C2 * windowLength N ε / Real.log N ^ B)
    (by norm_num) (pieceSum_add 3 4 N (localization N ε))
    (hC1 N ((le_max_left _ _).trans hN))
    (hC2 N ((le_max_right _ _).trans hN))
  convert hb using 1 <;> ring

#print axioms region4_lower
#print axioms remainder_lower
#print axioms group3_lower_from_parts
end
end LeanLab.Languasco2004.Decomp548c
