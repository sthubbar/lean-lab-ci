/-
Jia 1996 pages 270 to 273, the group 1 remainder transfer in Lemma 24.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The analytic transfer remains OPEN. The full numerical subtotal is separate.
The sealed Decomp548a file is not imported or edited.
-/
import LeanLab.Languasco2004.Decomp566a
import LeanLab.Languasco2004.Decomp566b

namespace LeanLab.Languasco2004.Decomp566c
open Finset Real Decomp279a Decomp316c GroupSplit548 RemainderData566 Decomp566b
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 270 to 273 support: the strict failure set is the smallest exceptional set
for the remainder transfer at fixed parameters. This is finite bookkeeping only. -/
theorem remainder_exception_iff (N ε η K : ℝ) :
    (∃ E : Finset ℕ, (E.card : ℝ) ≤ K ∧
      ∀ n ∈ window N ε, n ∉ E →
        model * scale N (localization N ε) n ≤
          pieceSum 1 11 false N (localization N ε) n +
            η * scale N (localization N ε) n) ↔
    (((window N ε).filter (fun n =>
      pieceSum 1 11 false N (localization N ε) n +
        η * scale N (localization N ε) n <
          model * scale N (localization N ε) n)).card : ℝ) ≤ K := by
  constructor
  · rintro ⟨E, hE, hgood⟩
    have hsub : (window N ε).filter (fun n =>
        pieceSum 1 11 false N (localization N ε) n +
          η * scale N (localization N ε) n <
            model * scale N (localization N ε) n) ⊆ E := by
      intro n hn
      obtain ⟨hns, hbad⟩ := mem_filter.mp hn
      by_contra hne
      exact (not_lt_of_ge (hgood n hns hne)) hbad
    exact (show (((window N ε).filter (fun n =>
      pieceSum 1 11 false N (localization N ε) n +
        η * scale N (localization N ε) n <
          model * scale N (localization N ε) n)).card : ℝ) ≤ E.card by
      exact_mod_cast card_le_card hsub).trans hE
  · intro h
    refine ⟨(window N ε).filter (fun n =>
      pieceSum 1 11 false N (localization N ε) n +
        η * scale N (localization N ε) n <
          model * scale N (localization N ε) n), h, ?_⟩
    intro n hn hne
    exact le_of_not_gt (fun hbad => hne (mem_filter.mpr ⟨hn, hbad⟩))

/-- Pages 270 to 273 support: an error budget at least the model needs no exceptions.
This special case uses only nonnegativity, not a prime distribution estimate. -/
theorem remainder_transfer_of_model_le (η : ℝ) (hη : model ≤ η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∃ E : Finset ℕ,
      (E.card : ℝ) ≤ C * windowLength N ε / Real.log N ^ B ∧
      ∀ n ∈ window N ε, n ∉ E →
        model * scale N (localization N ε) n ≤
          pieceSum 1 11 false N (localization N ε) n +
            η * scale N (localization N ε) n := by
  refine ⟨1, by norm_num, ?_⟩
  intro ε B hε _ _
  refine ⟨0, 1, ?_⟩
  intro N hN
  refine ⟨∅, by simp, ?_⟩
  intro n _ _
  have hY : 1 ≤ localization N ε := by
    unfold localization
    exact Real.one_le_rpow hN (by linarith)
  exact (mul_le_mul_of_nonneg_right hη (Decomp316a.scale_nonneg n hN hY)).trans
    (le_add_of_nonneg_left (pieceSum_nonneg 1 11 false N (localization N ε) n))

/-- LEAF. Jia pages 270 to 273, Lemma 24, the remainder equality and following lower bound.
The prime transfer follows the Omega11 argument using the applicable mean value regions
and Lemmas 18 and 21. Lemma 20 supplies the global 0.5607 lower kernel.
The numerical evaluation of the 25 explicit integrals is not an input to this leaf.
Every sealed cap, strict endpoint and region priority remains explicit through pieceSum.
The unnumbered lower integrals support display 65 on page 286. -/
theorem remainder_transfer :
    ∀ η : ℝ, 0 < η →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∃ E : Finset ℕ,
      (E.card : ℝ) ≤ C * windowLength N ε / Real.log N ^ B ∧
      ∀ n ∈ window N ε, n ∉ E →
        model * scale N (localization N ε) n ≤
          pieceSum 1 11 false N (localization N ε) n + η * scale N (localization N ε) n := by
  intro η hη
  by_cases hlarge : model ≤ η
  · exact remainder_transfer_of_model_le η hlarge
  · have hcount :
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
        ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
          (((window N ε).filter (fun n =>
            pieceSum 1 11 false N (localization N ε) n +
              η * scale N (localization N ε) n <
                model * scale N (localization N ε) n)).card : ℝ) ≤
            C * windowLength N ε / Real.log N ^ B := by
        have hlt : η < model := lt_of_not_ge hlarge
        exact Decomp566b.remainder_transfer_count η hlt
    obtain ⟨ε₀, hε₀, h⟩ := hcount
    refine ⟨ε₀, hε₀, ?_⟩
    intro ε B hε hεε₀ hB
    obtain ⟨C, N₀, hC⟩ := h ε B hε hεε₀ hB
    exact ⟨C, N₀, fun N hN =>
      (remainder_exception_iff N ε η
        (C * windowLength N ε / Real.log N ^ B)).mpr (hC N hN)⟩

/-- Jia page 273: the exact sealed remainder_lower statement follows from the complete
numerical certificate and its transfer. CONDITIONAL ON remainder_transfer only. -/
theorem remainder_lower_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 1 11 false N (localization N ε) n <
        0.394965 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e, he, h⟩ := remainder_transfer 0.0000002 (by norm_num)
  refine ⟨e, he, ?_⟩
  intro ε B hε hεe hB
  obtain ⟨C, N₀, hC⟩ := h ε B hε hεe hB
  refine ⟨C, max N₀ 1, ?_⟩
  intro N hN
  obtain ⟨E, hE, hgood⟩ := hC N ((le_max_left _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hY : 1 ≤ localization N ε := by
    unfold localization
    exact Real.one_le_rpow hN1 (by linarith)
  have hc := Decomp566a.count_transfer (window N ε) E
    (pieceSum 1 11 false N (localization N ε)) (scale N (localization N ε))
    model 0.394965 0.0000002
    (by linarith [remainder_model_lower])
    (fun n _ => Decomp316a.scale_nonneg n hN1 hY) hgood
  exact hc.trans hE

#print axioms remainder_exception_iff
#print axioms remainder_transfer_of_model_le
#print axioms remainder_transfer
#print axioms remainder_lower_from_parts
end
end LeanLab.Languasco2004.Decomp566c
