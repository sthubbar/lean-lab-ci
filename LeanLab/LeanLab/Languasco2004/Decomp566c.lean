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

/-- LEAF. Jia pages 270 to 273, Lemma 24, the remainder equality and following lower bound.
The prime transfer follows the Omega11 argument using the applicable mean value regions
and Lemmas 18 and 21. Lemma 20 supplies the global 0.5607 lower kernel.
The numerical evaluation of the 25 explicit integrals is not an input to this leaf.
Every sealed cap, strict endpoint and region priority remains explicit through pieceSum. -/
theorem remainder_transfer :
    ∀ η : ℝ, 0 < η →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∃ E : Finset ℕ,
      (E.card : ℝ) ≤ C * windowLength N ε / Real.log N ^ B ∧
      ∀ n ∈ window N ε, n ∉ E →
        model * scale N (localization N ε) n ≤
          pieceSum 1 11 false N (localization N ε) n + η * scale N (localization N ε) n := by sorry

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

#print axioms remainder_transfer
#print axioms remainder_lower_from_parts
end
end LeanLab.Languasco2004.Decomp566c
