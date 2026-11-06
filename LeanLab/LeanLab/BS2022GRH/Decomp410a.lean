/- AI wrote this Lean code for CODEX task410.
Ordinary RH Mertens input for journal Lemma 10 p. 1227.
Goldbach is open. -/
import LeanLab.BS2022GRH.Density410
import LeanLab.BS2022GRH.RH148
import LeanLab.BS2022GRH.Mertens410

namespace LeanLab.BS2022GRH.Decomp410a
open Real Finset ChenThresholdGRH
noncomputable section

/-- LEAF. Schoenfeld Corollary 2 p. 340 display 6.21, upper half.
The written proof on p. 340 is used in Corollary 3 p. 341 display 6.27.
The common constant is the proved prime reciprocal limit. Restrict to x at least 64.
Source https://doi.org/10.1090/S0025-5718-1976-0457374-X. -/
theorem rh_reciprocal_upper (hRH : RiemannHypothesis) (x : ℝ) (hx : 64 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) ≤
      log (log x) + DecompC169c.mertensConstant + (3 * log x + 4) / (8 * π * √x) := by
  sorry

/-- The lower half of Schoenfeld Corollary 3 p. 341 display 6.23.
The finite logarithmic correction and exponential inequality are proved.
CONDITIONAL ON the sharp RH reciprocal estimate. -/
theorem rh_mertens_lower (hRH : RiemannHypothesis) (x : ℝ) (hx : 64 ≤ x) :
    exp (-eulerMascheroniConstant) / log x *
      (1 - (3 * log x + 5) / (8 * π * √x)) ≤
        ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - 1 / (p : ℝ)) := by
  apply Mertens410.ordinary_product_lower_of_reciprocal x _ (by linarith)
  have h := rh_reciprocal_upper hRH x hx
  have he : (3 * log x + 4) / (8 * π * √x) ≤ (3 * log x + 5) / (8 * π * √x) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- The exact sealed density_lower statement from the ordinary Mertens leaf
and the clean finite corrections. Journal Lemma 10 p. 1227.
CONDITIONAL ON the open Schoenfeld leaf. -/
theorem density_lower (n : ℕ) (hG : GRH) (hn : (4e18 : ℝ) ≤ n) (hev : Even n) :
    8 * UNfull n / log n * (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤
      DecompC169a.density n := by
  apply Density410.density_lower_of_mertens n hn hev
  apply rh_mertens_lower (RH148.rh_of_grh hG)
  change (64 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ)
  rw [one_div]
  apply (le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 64)
    (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 8)).mpr
  rw [show (8 : ℝ) = (8 : ℕ) by norm_num, rpow_natCast]
  calc
    (64 : ℝ) ^ (8 : ℕ) = 281474976710656 := by norm_num
    _ ≤ (n : ℝ) := by linarith

end
end LeanLab.BS2022GRH.Decomp410a
#print axioms LeanLab.BS2022GRH.Decomp410a.rh_mertens_lower

#print axioms LeanLab.BS2022GRH.Decomp410a.density_lower

#print axioms LeanLab.BS2022GRH.Decomp410a.rh_reciprocal_upper
