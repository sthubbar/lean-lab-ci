/-
Jia 1996 pages 282 to 285, Lemma 28.
Source https://doi.org/10.4064/aa-77-3-207-287.
Four strictly smaller analytic leaves supply the exact sealed region1_lower statement.
The original leaf remains unchanged. The assembly is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Source565
import LeanLab.Languasco2004.Numeric565

namespace LeanLab.Languasco2004.Decomp565a
open Finset Real Decomp279a Decomp316a GroupSplit548 Source565 Numeric565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Jia page 283 display 58 and page 284 display 62.
The two Iwaniec sieve transfers are isolated before low cutoff cancellation.
The proof uses the progression estimate of Lemma 17 on page 253 and Lemma 16 on page 252. -/
theorem iwaniec_transfer :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.0000001 * scale N (localization N ε) n < iwaniecError true N (localization N ε) n ε)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia page 260 Lemma 19, specialized on page 283 display 59 and page 284 display 63.
Only the transfers of the removed low cutoff terms occur here. -/
theorem lemma19_transfer :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.0000001 * scale N (localization N ε) n < lemma19Error true N (localization N ε) n ε)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia page 283 display 60 and page 285 remaining region formula.
Only the model pair sum is compared with its Buchstab integral lower bound.
The numerical reserve includes the source exponent truncation and asymptotic errors. -/
theorem model_pair_lower :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        modelPair true N (localization N ε) n < (mainOne + 0.0000004) * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia pages 284 and 285 after display 63, using Lemma 20 on pages 261 and 262.
Only the model triple sum is bounded by its three reduced logarithmic integrals. -/
theorem model_triple_upper :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        (tripleOne + tripleTwo + tripleThree + 0.0000001) * scale N (localization N ε) n < modelTriple true N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Jia page 285 display 64 and the remaining seven regions.
CONDITIONAL ON the four analytic transfer and model leaves above.
This has the exact sealed region1_lower type and no admission of its own. -/
theorem region1_lower_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 5 1 true N (localization N ε) n <
        0.468045 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  let P0 : ℝ → ℝ → ℕ → Prop := fun ε N n => 0.0000001 * scale N (localization N ε) n < iwaniecError true N (localization N ε) n ε
  let P1 : ℝ → ℝ → ℕ → Prop := fun ε N n => 0.0000001 * scale N (localization N ε) n < lemma19Error true N (localization N ε) n ε
  let P2 : ℝ → ℝ → ℕ → Prop := fun ε N n => modelPair true N (localization N ε) n < (mainOne + 0.0000004) * scale N (localization N ε) n
  let P3 : ℝ → ℝ → ℕ → Prop := fun ε N n => (tripleOne + tripleTwo + tripleThree + 0.0000001) * scale N (localization N ε) n < modelTriple true N (localization N ε) n
  have h01 := exceptional_union P0 P1 iwaniec_transfer lemma19_transfer
  have h23 := exceptional_union P2 P3 model_pair_lower model_triple_upper
  have hu := exceptional_union (fun ε N n => P0 ε N n ∨ P1 ε N n)
    (fun ε N n => P2 ε N n ∨ P3 ε N n) h01 h23
  obtain ⟨e, he, hu⟩ := hu
  refine ⟨min e ((16 / 135 : ℝ)^3), lt_min he (by norm_num), ?_⟩
  intro ε B hε heps hB
  obtain ⟨C, N₀, hC⟩ := hu ε B hε (heps.trans_le (min_le_left _ _)) hB
  refine ⟨C, max N₀ 2, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hY : 1 ≤ localization N ε := by
    unfold localization
    exact Real.one_le_rpow (by linarith) (by linarith)
  have hz : (localization N ε) ^ delta ε ≤ (localization N ε) ^ (16 / 135 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY
      (delta_cutoff ε hε (heps.trans_le (min_le_right _ _)).le)
  have hsub : (window N ε).filter (fun n => pieceSum 5 1 true N (localization N ε) n <
      0.468045 * scale N (localization N ε) n) ⊆
      @Finset.filter ℕ (fun n => (P0 ε N n ∨ P1 ε N n) ∨ (P2 ε N n ∨ P3 ε N n))
        (fun n => Classical.propDecidable _) (window N ε) := by
    intro n hn
    obtain ⟨hnw, hn⟩ := mem_filter.mp hn
    apply (@Finset.mem_filter ℕ
      (fun n => (P0 ε N n ∨ P1 ε N n) ∨ (P2 ε N n ∨ P3 ε N n))
      (fun n => Classical.propDecidable _) (window N ε) n).mpr
    refine ⟨hnw, ?_⟩
    by_contra hbad
    have hg := not_or.mp hbad
    have hg0 := not_or.mp hg.1
    have hg1 := not_or.mp hg.2
    have hI : iwaniecError true N (localization N ε) n ε ≤
        0.0000001 * scale N (localization N ε) n := le_of_not_gt hg0.1
    have h19 : lemma19Error true N (localization N ε) n ε ≤
        0.0000001 * scale N (localization N ε) n := le_of_not_gt hg0.2
    have hP : (mainOne + 0.0000004) * scale N (localization N ε) n ≤
        modelPair true N (localization N ε) n := le_of_not_gt hg1.1
    have hT : modelTriple true N (localization N ε) n ≤
        (tripleOne + tripleTwo + tripleThree + 0.0000001) * scale N (localization N ε) n := le_of_not_gt hg1.2
    have hs := scale_nonneg n (by linarith : 1 ≤ N) hY
    have hp := pointwise_from_transfers true N (localization N ε) n ε
      mainOne (tripleOne + tripleTwo + tripleThree) hz hs hI h19 hP hT
    have hc : (0.468045 : ℝ) ≤ mainOne - (tripleOne + tripleTwo + tripleThree) := by
      nlinarith [region1_numeric]
    have hm := mul_le_mul_of_nonneg_right hc hs
    linarith
  have hcard : (((window N ε).filter (fun n => pieceSum 5 1 true N (localization N ε) n <
      0.468045 * scale N (localization N ε) n)).card : ℝ) ≤
      ((@Finset.filter ℕ (fun n => (P0 ε N n ∨ P1 ε N n) ∨ (P2 ε N n ∨ P3 ε N n))
        (fun n => Classical.propDecidable _) (window N ε)).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hcard.trans (hC N ((le_max_left _ _).trans hN))

#print axioms iwaniec_transfer
#print axioms lemma19_transfer
#print axioms model_pair_lower
#print axioms model_triple_upper
#print axioms region1_lower_from_parts
end
end LeanLab.Languasco2004.Decomp565a
