/-
Jia 1996 page 270, the Omega11 transfer in Lemma 24.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The numerical integral is separate from the OPEN analytic transfer.
The sealed Decomp548a file is not imported or edited.
-/
import LeanLab.Languasco2004.Numeric11_566
import LeanLab.Languasco2004.GroupSplit548
import LeanLab.Languasco2004.Decomp316a

namespace LeanLab.Languasco2004.Decomp566a
open Finset Real Decomp279a Decomp316c GroupSplit548 Numeric11_566
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 270 support: a model lower bound outside E bounds the finite failure count.
This finite implication has no analytic premise. -/
theorem count_transfer (s E : Finset ℕ) (f g : ℕ → ℝ) (I c η : ℝ)
    (hI : c + η ≤ I) (hg : ∀ n ∈ s, 0 ≤ g n)
    (hgood : ∀ n ∈ s, n ∉ E → I * g n ≤ f n + η * g n) :
    ((s.filter (fun n => f n < c * g n)).card : ℝ) ≤ (E.card : ℝ) := by
  exact_mod_cast card_le_card (show s.filter (fun n => f n < c * g n) ⊆ E by
    intro n hn
    obtain ⟨hns, hbad⟩ := mem_filter.mp hn
    by_contra hne
    have hmodel := hgood n hns hne
    have hmul := mul_le_mul_of_nonneg_right hI (hg n hns)
    nlinarith)

/-- LEAF. Jia page 270, Lemma 24, the three equalities before its final numerical bound.
Lemma 8 region i supplies display 8, Lemma 18 supplies the exceptional prime transfer,
and Lemma 21 on page 262 supplies the sifted integer model.
For each fixed error budget, sufficiently small epsilon gives this one sided transfer.
The numerical evaluation of model11 is not an input to this leaf.
These unnumbered Omega11 equalities support display 65 on page 286.
The mean value input is display 32 on page 253. -/
theorem region11_transfer :
    ∀ η : ℝ, 0 < η →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∃ E : Finset ℕ,
      (E.card : ℝ) ≤ C * windowLength N ε / Real.log N ^ B ∧
      ∀ n ∈ window N ε, n ∉ E →
        model11 * scale N (localization N ε) n ≤
          pieceSum 1 11 true N (localization N ε) n + η * scale N (localization N ε) n := by
  intro η hη
  by_cases hle : model11 ≤ η
  · -- η ≥ model11: scale and pieceSum are nonnegative, so E := ∅ works for every N ≥ 2.
    have h_easy : ∀ (e : ℝ), 0 < e → model11 ≤ e →
        (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
          ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∃ E : Finset ℕ,
            (E.card : ℝ) ≤ C * windowLength N ε / Real.log N ^ B ∧
            ∀ n ∈ window N ε, n ∉ E →
              model11 * scale N (localization N ε) n ≤
                pieceSum 1 11 true N (localization N ε) n + e * scale N (localization N ε) n) := by
      intro e he hle
      use 1, 2
      constructor <;> norm_num
      intro ε B hε hεe hB
      use 0, 2
      intro N hN
      use ∅
      constructor <;> norm_num [Finset.card_empty]
      intro n hn hne
      have hscale : 0 ≤ scale N (localization N ε) n := by
        have hN : 1 ≤ N := by linarith
        have hY : 1 ≤ localization N ε := by
          have hN₁ : 1 < N := by linarith
          have h₁ : 1 ≤ N ^ (7 / 12 + ε) := Real.one_le_rpow hN (by linarith)
          simpa [localization] using h₁
        exact Decomp316a.scale_nonneg n hN hY
      have hpiece : 0 ≤ pieceSum 1 11 true N (localization N ε) n :=
        pieceSum_nonneg 1 11 true N (localization N ε) n
      nlinarith [hscale, hpiece]
    exact h_easy η hη hle
  · -- η < model11: the remaining integers require Jia 1996 Lemma 24's Omega11
    -- single-region exceptional-set estimate, which is not available in Mathlib
    -- or in this repository (every sibling region transfer stays CONDITIONAL on OPEN leaves).
    sorry

/-- Jia page 270: the exact sealed region11_lower statement follows from the numerical
certificate and the analytic transfer. CONDITIONAL ON region11_transfer only. -/
theorem region11_lower_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 1 11 true N (localization N ε) n <
        0.027761 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e, he, h⟩ := region11_transfer 0.0000003 (by norm_num)
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
  have hc := count_transfer (window N ε) E
    (pieceSum 1 11 true N (localization N ε)) (scale N (localization N ε))
    model11 0.027761 0.0000003
    (by linarith [model11_lower])
    (fun n _ => Decomp316a.scale_nonneg n hN1 hY) hgood
  exact hc.trans hE

/-- Page 270 support: a nonempty finite model satisfies the transfer premises. -/
theorem count_transfer_instance :
    ((({0} : Finset ℕ).filter (fun _ => (2 : ℝ) < 1 * 1)).card : ℝ) ≤ 0 := by
  have h := count_transfer ({0} : Finset ℕ) ∅ (fun _ => (2 : ℝ)) (fun _ => 1)
    2 1 1 (by norm_num) (by intro n hn; norm_num) (by intro n hn hne; norm_num)
  simpa using h

#print axioms count_transfer
#print axioms region11_transfer
#print axioms region11_lower_from_parts
#print axioms count_transfer_instance
end
end LeanLab.Languasco2004.Decomp566a
