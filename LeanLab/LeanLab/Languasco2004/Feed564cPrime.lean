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

/-- PROVED, formerly LEAF: Jia page 282 clipping, for n in the basic interval every prime pair of regions 53
and 66 satisfies Y^(16/135) < q < min p (sqrt (2Y/p)) and p ≤ sqrt (2Y), so the unclipped
prime sum is a subsum of the clipped prime model. MEDIUM -/
theorem pairModel12_le_primeModel :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ n ∈ window N ε,
        pairModel labels12 N (localization N ε) n ≤ primeModel labels12 N (localization N ε) n :=
  ⟨1, one_pos, fun ε hε _ => ⟨2, fun N hN n _ =>
    pairModel_le_primeModel_of_clip labels12 N _ n
      (clip12 _ (one_lt_localization N ε hN hε))⟩⟩

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
