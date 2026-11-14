/-
Jia 1996 Lemma 27, pages 280 to 282, supporting display 65 on page 286.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
Two proper analytic steps remain OPEN. The assembly is also CONDITIONAL
ON the OPEN computational integral inputs in Polynomial564s.
-/
import LeanLab.Languasco2004.Model564
import LeanLab.Languasco2004.Numeric564

namespace LeanLab.Languasco2004.Decomp564b
open Finset Real Decomp279a Model564 RemainderData564 Numeric564
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Jia pages 231 to 233 and 280 to 281, Lemmas 11 and 27.
Lemma 18 display 32 on page 253 and its page 260 exceptional set argument
transfer only regions 33, 36, 38, 40, 42, 46 and 49 to their arithmetic B model.
No deterministic Buchstab evaluation is asserted here. -/
theorem prime_to_rough11 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        primeModel labels11 N (localization N ε) n + δ * scale N (localization N ε) n <
          singular n / Real.log N * roughModel labels11 (localization N ε))).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF. Jia pages 261, 262, 280, 281 and 282, display 40 and Lemmas 20, 21 and 27.
Only the arithmetic B model of regions 33, 36, 38, 40, 42, 46 and 49 is bounded by its
proper subfamily of the printed lower integrals. The numerical evaluation
is proved separately. The global Buchstab bound is part of this analytic input. -/
theorem rough11_to_integral (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → 2 ≤ Y →
      (integral11 - δ) * Y / Real.log Y ≤ roughModel labels11 Y := by sorry

/-- Jia Lemma 27: this proper mean value family has its printed subtotal.
CONDITIONAL ON prime_to_rough11 and rough11_to_integral.
The pointwise polynomial comparison and finite tolerance absorption are proved.
The numerical subtotal still depends on the OPEN short_integral inputs. -/
theorem family11_lower_from_transfers :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => primeModel labels11 N (localization N ε) n <
        0.014887 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  exact lower_from_model (primeModel labels11) labels11 integral11 0.014887
    (lt_of_lt_of_le (by norm_num : (0.014887 : ℝ) < 0.0148871) integral11_lower)
    prime_to_rough11 rough11_to_integral

#print axioms prime_to_rough11
#print axioms rough11_to_integral
#print axioms family11_lower_from_transfers
end
end LeanLab.Languasco2004.Decomp564b
