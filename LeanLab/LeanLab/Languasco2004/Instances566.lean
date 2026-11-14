/-
Jia 1996 pages 270 to 273, concrete domains for task566 support.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Midpoint566
import LeanLab.Languasco2004.RemainderData566

namespace LeanLab.Languasco2004.Instances566
open Real RemainderData566 Midpoint566
noncomputable section

/-- Page 270 support: both Omega11 pieces have strict rational interior points. -/
theorem omega11_interiors :
    (17 / 63 : ℚ) < 7 / 25 ∧ (7 / 25 : ℚ) < 17 / 57 ∧
      (17 / 30 - 6 / 5 * (7 / 25) : ℚ) < 47 / 200 ∧
      (47 / 200 : ℚ) < (1 - 7 / 25) / 3 ∧
      ((1 - 7 / 25) / 3 : ℚ) < 1 / 4 ∧
      (1 / 4 : ℚ) < 7 / 24 - (7 / 25) / 8 := by norm_num

/-- Pages 271 to 273 support: every remainder term has a strict rational interior point. -/
theorem remainder_interiors : ∀ i : Fin 25,
    let r := data i
    let t := (r 0 + r 1) / 2
    let u := (r 2 * t + r 3 + (r 4 * t + r 5)) / 2
    r 0 < t ∧ t < r 1 ∧ r 2 * t + r 3 < u ∧ u < r 4 * t + r 5 := by
  decide +kernel

/-- Pages 270 to 273 support: a reciprocal sample above the centre meets the midpoint hypotheses. -/
theorem midpoint_instance :
    0 ≤ Numeric30_548.invPoly3 (3 / 2) 1 ∧
      Numeric30_548.invPoly3 (3 / 2) 1 ≤ (1 / (3 / 2) : ℝ) ∧
      0 ≤ Numeric548.invPoly5 (3 / 2) 1 ∧
      Numeric548.invPoly5 (3 / 2) 1 ≤ (1 / (3 / 2) : ℝ) := by
  obtain ⟨h1, h2⟩ := invPoly3_midpoint (3 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨h3, h4⟩ := invPoly5_midpoint (3 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h1, h2, h3, h4⟩

/-- Pages 270 to 273 support: both logarithm polynomials have an attained zero endpoint. -/
theorem logarithm_endpoint_instance : Real.log 1 = 0 ∧
    2 * (((1 : ℝ) - 1) / (1 + 1)) + 2 / 3 * (((1 : ℝ) - 1) / (1 + 1))^3 = 0 := by
  norm_num

#print axioms omega11_interiors
#print axioms remainder_interiors
#print axioms midpoint_instance
#print axioms logarithm_endpoint_instance
end
end LeanLab.Languasco2004.Instances566
