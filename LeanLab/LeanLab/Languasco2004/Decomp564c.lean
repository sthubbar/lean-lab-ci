/-
Jia 1996 Lemma 27, pages 280 to 282, supporting display 65 on page 286.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Two proper analytic steps remain OPEN. The assembly is also CONDITIONAL
ON the OPEN computational integral inputs in Polynomial564s.
-/
import LeanLab.Languasco2004.Decomp564b
import LeanLab.Languasco2004.Numeric564

namespace LeanLab.Languasco2004.Decomp564c
open Finset Real Decomp279a GroupSplit548 Model564 RemainderData564 Numeric564
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Jia pages 233 to 235 and 281 to 282, Lemmas 12 and 27.
Lemma 18 display 32 on page 253 and its page 260 exceptional set argument
transfer only regions 53 and 66 to their arithmetic B model.
No deterministic Buchstab evaluation is asserted here. -/
theorem prime_to_rough12 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        primeModel labels12 N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel labels12 (localization N ε))).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia pages 261, 262, 280, 281 and 282, display 40 and Lemmas 20, 21 and 27.
Only the arithmetic B model of regions 53 and 66 is bounded by its
proper subfamily of the printed lower integrals. The numerical evaluation
is proved separately. The global Buchstab bound is part of this analytic input. -/
theorem rough12_to_integral (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → 2 ≤ Y →
      (integral12 - δ) * Y / Real.log Y ≤ roughModel labels12 Y := by sorry

/-- Jia Lemma 27: this proper mean value family has its printed subtotal.
CONDITIONAL ON prime_to_rough12 and rough12_to_integral.
The pointwise polynomial comparison and finite tolerance absorption are proved.
The numerical subtotal still depends on the OPEN short_integral inputs. -/
theorem family12_lower_from_transfers :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => primeModel labels12 N (localization N ε) n <
        0.009392 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  exact lower_from_model (primeModel labels12) labels12 integral12 0.009392
    (lt_of_lt_of_le (by norm_num : (0.009392 : ℝ) < 0.0093921) integral12_lower)
    prime_to_rough12 rough12_to_integral

/-- Jia page 282: the two proper mean value families give the exact sealed remainder_lower.
CONDITIONAL ON the four source transfers and the eight OPEN computational integral inputs.
There is no admission in this finite exceptional set assembly. -/
theorem remainder_lower_from_transfers :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 4 30 false N (localization N ε) n <
        0.024279 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e1, he1, h1⟩ := Decomp564b.family11_lower_from_transfers
  obtain ⟨e2, he2, h2⟩ := family12_lower_from_transfers
  refine ⟨min e1 e2, lt_min he1 he2, ?_⟩
  intro ε B hε he hB
  obtain ⟨C1, N1, hC1⟩ := h1 ε B hε (he.trans_le (min_le_left _ _)) hB
  obtain ⟨C2, N2, hC2⟩ := h2 ε B hε (he.trans_le (min_le_right _ _)) hB
  refine ⟨C1+C2, max N1 N2, ?_⟩
  intro N hN
  have h := GroupSplit548.combine_counts (window N ε)
    (primeModel labels11 N (localization N ε))
    (primeModel labels12 N (localization N ε))
    (pieceSum 4 30 false N (localization N ε))
    (scale N (localization N ε)) 0.014887 0.009392 0.024279
    (C1 * windowLength N ε / Real.log N ^ B)
    (C2 * windowLength N ε / Real.log N ^ B)
    (by norm_num) (primeModel_remainder N (localization N ε))
    (hC1 N ((le_max_left _ _).trans hN)) (hC2 N ((le_max_right _ _).trans hN))
  convert h using 1 <;> ring

#print axioms remainder_lower_from_transfers
#print axioms prime_to_rough12
#print axioms rough12_to_integral
#print axioms family12_lower_from_transfers
end
end LeanLab.Languasco2004.Decomp564c
