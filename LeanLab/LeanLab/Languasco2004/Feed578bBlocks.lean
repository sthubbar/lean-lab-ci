/-
Jia 1996 page 260 Lemma 19, as used in page 283 display 59 and page 284 display 63.
Source https://doi.org/10.4064/aa-77-3-207-287.
The dyadic block union of Lemma 19 shared by the two removed layer transfers. It remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp565d
import LeanLab.Languasco2004.Feed578bBlocks19

namespace LeanLab.Languasco2004.Feed578bBlocks
open Finset Real Decomp279a Decomp316a Source565 Decomp565d
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Displays 59 and 63 support: a pointwise reduction with slack 0.00000004 times the scale
leaves only the block error above 0.00000001 times the scale on the exceptional set. -/
theorem count_transfer (s : Finset ℕ) (E sc G : ℕ → ℝ)
    (h : ∀ n ∈ s, E n ≤ 0.00000004 * sc n + G n) :
    ((s.filter (fun n => 0.00000005 * sc n < E n)).card : ℝ) ≤
      ((s.filter (fun n => 0.00000001 * sc n < G n)).card : ℝ) := by
  exact_mod_cast card_le_card (by
    intro n hn
    obtain ⟨hn, hbad⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hn, ?_⟩
    have := h n hn
    linarith)

/-- LEAF: Jia page 260 Lemma 19 summed over at most K log N dyadic blocks with constants uniform in the block data, HARD.
Lemma 19 holds with implicit constants depending only on epsilon and B. A union over
K log N blocks at a larger exponent bounds the summed absolute errors by D times C of n
times the summed model counts over log N squared plus a negligible term. When the summed
model counts are at most K₂ Y over log Y, this is below 0.00000001 times the scale for large N,
since C of n is bounded below on even n. The sealed Decomp565d.lemma19_rough_input lets its
constants depend on M and the weights, so it does not yield this union directly. -/
theorem lemma19_blocks_uniform :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ (K K₂ : ℝ) (M : ℕ → ℝ → ℝ) (w : ℕ → ℝ → ℕ → ℝ),
      (∀ j : ℕ, ∀ N : ℝ, 2 ≤ N →
        (localization N ε) ^ (119 / 135 : ℝ) ≤ M j N ∧
          M j N ≤ (localization N ε) ^ (1 - delta ε)) →
      (∀ j : ℕ, ∀ N : ℝ, ∀ m : ℕ, 0 ≤ w j N m ∧ w j N m ≤ 1) →
      (∀ j : ℕ, ∀ N : ℝ, 2 ≤ N → ∀ m p : ℕ, p.Prime → p ∣ m →
        (p : ℝ) < (localization N ε) ^ delta ε → w j N m = 0) →
      (∃ T : ℝ, ∀ N : ℝ, T ≤ N → ∀ n ∈ window N ε,
        ∑ j ∈ range ⌈K * log N⌉₊,
          weightedCofactors true N (localization N ε) (M j N) n (w j N) ≤
        K₂ * localization N ε / log (localization N ε)) →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000001 * scale N (localization N ε) n <
          ∑ j ∈ range ⌈K * log N⌉₊,
            |weightedCofactors false N (localization N ε) (M j N) n (w j N) -
              singular n / log N *
                weightedCofactors true N (localization N ε) (M j N) n (w j N)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B :=
  Feed578bBlocks19.lemma19_blocks_uniform_from_leaves

#print axioms count_transfer
#print axioms lemma19_blocks_uniform
end
end LeanLab.Languasco2004.Feed578bBlocks
