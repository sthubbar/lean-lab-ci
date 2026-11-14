/-
Jia 1996 Lemma 27, pages 280 and 281, supporting display 65 on page 286.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Two analytic transfers remain OPEN. The exact assembly is CONDITIONAL.
This file does not import Decomp548d or any module importing it.
-/
import LeanLab.Languasco2004.Model564

namespace LeanLab.Languasco2004.Decomp564a
open Finset Real Decomp279a Decomp316a GroupSplit548 Model564 Numeric30_548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Jia pages 280 and 281, Lemma 27, the first integral identity.
Use Lemma 11 region i on pages 231 to 233 and Lemma 18 display 32
on page 253, followed by the exceptional set argument on page 260.
Only the prime count to the arithmetic B model comparison is asserted.
The positive tolerance is independent of the logarithmic saving B. -/
theorem prime_to_rough30 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        pieceSum 4 30 true N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel {30} (localization N ε))).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia pages 261, 262, 270 and 281, display 40 and Lemma 21.
Only the deterministic arithmetic B model is evaluated. The complete first
integral is kept exact. No prime representation or exceptional set occurs.
The strict finite endpoints and the prime caps are part of the model. -/
theorem rough30_to_integral (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → 2 ≤ Y →
      ((∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ) * Y / Real.log Y ≤
        roughModel {30} Y := by sorry

/-- Jia page 281: the numerical reserve absorbs both analytic tolerances.
CONDITIONAL ON prime_to_rough30 and rough30_to_integral.
This has the exact sealed region30_lower statement and no admission of its own. -/
theorem region30_lower_from_transfers :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 4 30 true N (localization N ε) n <
        0.000303 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  let δ : ℝ := 1 / 20000000
  have hδ : 0 < δ := by norm_num [δ]
  obtain ⟨e, he, hprime⟩ := prime_to_rough30 δ hδ
  obtain ⟨Y₀, hmodel⟩ := rough30_to_integral δ hδ
  refine ⟨e, he, ?_⟩
  intro ε B hε he' hB
  obtain ⟨C, M, hC⟩ := hprime ε B hε he' hB
  obtain ⟨L, hL⟩ := localization_large ε Y₀ hε
  refine ⟨C, max M L, ?_⟩
  intro N hN
  obtain ⟨hN2, hY⟩ := hL N ((le_max_right _ _).trans hN)
  have hY2 : 2 ≤ localization N ε := (le_max_left _ _).trans hY
  have hYM : Y₀ ≤ localization N ε := (le_max_right _ _).trans hY
  have hlog : 0 ≤ Real.log (localization N ε) := Real.log_nonneg (by linarith)
  have hcoeff : 0.000303 + δ ≤
      (∫ t in (34 / 99 : ℝ)..(1649 / 4752), inner30 t) - δ := by
    have := region30_numeric_margin
    dsimp [δ]
    linarith
  have hmod : (0.000303 + δ) * localization N ε / Real.log (localization N ε) ≤
      roughModel {30} (localization N ε) :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (by linarith)) hlog).trans
      (hmodel _ hYM hY2)
  have hs := bad_transfer (window N ε)
    (pieceSum 4 30 true N (localization N ε)) (scale N (localization N ε))
    (fun n => singular n / Real.log N * roughModel {30} (localization N ε))
    0.000303 δ
    (fun n _ => model_scale_lower {30} N (localization N ε) (0.000303 + δ) n hN2 hmod)
  have hc : (((window N ε).filter (fun n => pieceSum 4 30 true N (localization N ε) n <
      0.000303 * scale N (localization N ε) n)).card : ℝ) ≤
      (((window N ε).filter (fun n =>
        pieceSum 4 30 true N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel {30} (localization N ε))).card : ℝ) := by
    exact_mod_cast card_le_card hs
  exact hc.trans (hC N ((le_max_left _ _).trans hN))

#print axioms prime_to_rough30
#print axioms rough30_to_integral
#print axioms region30_lower_from_transfers
end
end LeanLab.Languasco2004.Decomp564a
