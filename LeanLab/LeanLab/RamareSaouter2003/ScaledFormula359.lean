import LeanLab.RamareSaouter2003.Decomp359d
import LeanLab.RamareSaouter2003.Decomp1531a

/-!
P0099 pp. 15 and 16, Lemma 4 after affine substitution.
The corrected general formula is the explicit hypothesis from Ramare 2023 p. 1.
This proves the specialization bridge and does not prove the cited formula.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.ScaledFormula359
open Real Chebyshev Smooth L3Zeta

/-- P0099 pp. 15 and 16 applied on p. 19 before display 13.
CONDITIONAL ON the corrected general weighted formula of Ramare 2023,
Lemma 1.1. The affine weight is continuously differentiable and all
integral substitutions are supplied by Mathlib. -/
theorem scaled_weight_formula_of_corrected (h : CorrectedLemma4_290.lemma4_corrected_stmt)
    (m : ℕ) (A δ : ℝ) (hm : 2 ≤ m) (hA : 2 ≤ A) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, ψ (A * (1 + δ * t)) * fm m t) =
      (∫ t in (0 : ℝ)..1, A * (1 + δ * t) * fm m t) -
      (∑' i : ZI, ∫ t in (0 : ℝ)..1,
        (((A * (1 + δ * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
          (i.1 : ℂ) * (fm m t : ℂ)).re -
      ∫ t in (0 : ℝ)..1,
        (Real.log (2 * π) + (1 / 2) *
          Real.log (1 - 1 / (A * (1 + δ * t)) ^ 2)) * fm m t := by
  let d := A * δ
  have hd : 0 < d := mul_pos (by linarith) hδ
  let g : ℝ → ℝ := fun y => fm m ((y - A) / d)
  have hcd : ContDiff ℝ 1 g :=
    ((Decomp1531a.contDiff_fm m).of_le (by simp)).comp (by fun_prop)
  have hid := h A (d + A) hA (by linarith) g hcd.contDiffOn
  have harg (t : ℝ) : (d * t + A - A) / d = t := by field_simp; ring
  have hlin (t : ℝ) : d * t + A = A * (1 + δ * t) := by dsimp [d]; ring
  have subR (f : ℝ → ℝ) :
      (∫ y in A..(d + A), f y * g y) =
        d * ∫ t in (0 : ℝ)..1, f (A * (1 + δ * t)) * fm m t := by
    have hh := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
      (fun y => f y * g y) d A
    simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at hh
    rw [← hh]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    change f (d * t + A) * fm m ((d * t + A - A) / d) = _
    rw [harg, hlin]
  have subC (f : ℝ → ℂ) :
      (∫ y in A..(d + A), f y * (g y : ℂ)) =
        (d : ℂ) * ∫ t in (0 : ℝ)..1, f (A * (1 + δ * t)) * (fm m t : ℂ) := by
    have hh := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
      (fun y => f y * (g y : ℂ)) d A
    simp only [mul_zero, zero_add, mul_one, Complex.real_smul] at hh
    rw [← hh]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    change f (d * t + A) * (fm m ((d * t + A - A) / d) : ℂ) = _
    rw [harg, hlin]
  simp_rw [subR, subC] at hid
  rw [tsum_mul_left, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hid
  simp only [zpow_neg, zpow_ofNat, one_div] at hid ⊢
  nlinarith

end LeanLab.RamareSaouter2003.ScaledFormula359
#print axioms LeanLab.RamareSaouter2003.ScaledFormula359.scaled_weight_formula_of_corrected
