/-
Jia 1996 Lemma 27, pages 281 and 282, with Lemma 12 on pages 233 to 235,
Lemma 18 display 32 on page 253 and its page 260 exceptional set argument.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Split of Decomp564c.prime_to_rough12 into cited LEAF steps, burst-20261122.
The generic assembly and pairModel are shared from Feed564bPrime.
The parent statement is proved below from the leaves, CONDITIONAL ON the open leaves.
-/
import LeanLab.Languasco2004.Feed564bPrime

namespace LeanLab.Languasco2004.Feed564cPrime
open Finset Real Decomp279a Decomp316c Model564 Feed564bPrime
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 282 clipping, for n in the basic interval every prime pair of regions 53
and 66 satisfies Y^(16/135) < q < min p (sqrt (2Y/p)) and p ≤ sqrt (2Y), so the unclipped
prime sum is a subsum of the clipped prime model. MEDIUM -/
theorem pairModel12_le_primeModel :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ n ∈ window N ε,
        pairModel labels12 N (localization N ε) n ≤ primeModel labels12 N (localization N ε) n := by
  use 1 / 12
  constructor
  · norm_num
  · intro ε hε he
    use 100
    intro N hN
    intro n hn
    set Y := localization N ε with hY
    have h₁ : pairModel labels12 N Y n ≤ primeModel labels12 N Y n := by
      have hY_pos : 0 < Y := by sorry
      have hY_ge1 : 1 ≤ Y := by sorry
      have h_2Y_le_N : 2 * Y ≤ N := by sorry
      have h_floor_le_n : ⌊2 * Y⌋₊ ≤ n := by sorry
      have h_clip : ∀ (p q : ℕ), p.Prime → q.Prime → regionIndex Y p q ∈ labels12 →
          Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y) ∧
          Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ))) := by sorry
      sorry
    exact h₁

/-- LEAF: Jia Lemma 12 pages 233 to 235 with Lemma 18 display 32 on page 253 and the page 260
exceptional set argument, applied to one source region D_i, i in 53, 66: outside an
exceptional set the prime sum S of A_pq and q over D_i is at least the singular factor over
log N times the arithmetic B model of D_i, minus delta times the main term. HARD -/
theorem region_transfer12 (i : ℕ) (hi : i ∈ labels12) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        pairModel {i} N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel {i} (localization N ε))).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Jia Lemma 27 pages 281 and 282: Decomp564c.prime_to_rough12 from the leaves.
CONDITIONAL ON pairModel12_le_primeModel and region_transfer12. Same type as the parent. -/
theorem prime_to_rough12_from_leaves (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        primeModel labels12 N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel labels12 (localization N ε))).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B :=
  prime_transfer_of_pair labels12 pairModel12_le_primeModel
    (transfer_of_regions labels12 ⟨53, by simp [labels12]⟩ region_transfer12) δ hδ

#print axioms pairModel12_le_primeModel
#print axioms region_transfer12
#print axioms prime_to_rough12_from_leaves
end
end LeanLab.Languasco2004.Feed564cPrime
