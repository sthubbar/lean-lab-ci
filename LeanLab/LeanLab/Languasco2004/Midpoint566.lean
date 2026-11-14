/-
Jia 1996 pages 270 to 273, supporting polynomial enclosures.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Numeric548
import LeanLab.Languasco2004.Numeric30_548

namespace LeanLab.Languasco2004.Midpoint566
open Real Numeric548 Numeric30_548
noncomputable section

/-- Pages 270 to 273 support: the four term reciprocal minorant allows a midpoint centre. -/
theorem invPoly3_midpoint (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hxc : x ≤ 2 * c) :
    0 ≤ invPoly3 x c ∧ invPoly3 x c ≤ 1 / x := by
  have hz : 0 ≤ 2 - x / c := by apply sub_nonneg.mpr; exact (div_le_iff₀ hc).mpr hxc
  have hp : invPoly3 x c = (2 - x / c) * (1 + (1 - x / c)^2) / c := by
    unfold invPoly3
    ring
  have he : invPoly3 x c * x = 1 - (1 - x / c)^4 := by
    unfold invPoly3
    field_simp
    ring
  constructor
  · rw [hp]
    positivity
  · apply (le_div_iff₀ hx).mpr
    nlinarith [sq_nonneg ((1 - x / c)^2)]

/-- Pages 270 to 273 support: the six term reciprocal minorant allows a midpoint centre. -/
theorem invPoly5_midpoint (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hxc : x ≤ 2 * c) :
    0 ≤ invPoly5 x c ∧ invPoly5 x c ≤ 1 / x := by
  have hz : 0 ≤ 2 - x / c := by apply sub_nonneg.mpr; exact (div_le_iff₀ hc).mpr hxc
  have hp : invPoly5 x c = (2 - x / c) * (1 + (1 - x / c)^2 + (1 - x / c)^4) / c := by
    unfold invPoly5
    ring
  have he : invPoly5 x c * x = 1 - (1 - x / c)^6 := by
    unfold invPoly5
    field_simp
    ring
  constructor
  · rw [hp]
    positivity
  · apply (le_div_iff₀ hx).mpr
    nlinarith [sq_nonneg ((1 - x / c)^3)]

/-- Pages 271 to 273 support: four odd terms from Mathlib minorize log y. -/
theorem log_odd_seven_lower (y : ℝ) (hy : 1 ≤ y) :
    2 * ((y - 1) / (y + 1)) + 2 / 3 * ((y - 1) / (y + 1)) ^ 3 +
      2 / 5 * ((y - 1) / (y + 1)) ^ 5 + 2 / 7 * ((y - 1) / (y + 1)) ^ 7 ≤ Real.log y := by
  have hden : 0 < y + 1 := by linarith
  have hz : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) hden.le
  have hz1 : (y - 1) / (y + 1) < 1 := (div_lt_one hden).mpr (by linarith)
  have h := Real.sum_range_le_log_div hz hz1 4
  have he : (1 + (y - 1) / (y + 1)) / (1 - (y - 1) / (y + 1)) = y := by
    field_simp
    <;> ring
  rw [he] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Pages 271 to 273 support: a two term midpoint reciprocal polynomial for high odd powers. -/
def invPoly1 (x c : ℝ) : ℝ := (2 - x / c) / c

/-- Pages 271 to 273 support: the two term minorant follows from the existing four term bound. -/
theorem invPoly1_midpoint (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (hxc : x ≤ 2 * c) :
    0 ≤ invPoly1 x c ∧ invPoly1 x c ≤ 1 / x := by
  have hz : 0 ≤ 2 - x / c := by apply sub_nonneg.mpr; exact (div_le_iff₀ hc).mpr hxc
  have hp : 0 ≤ invPoly1 x c := div_nonneg hz hc.le
  have he : invPoly3 x c = invPoly1 x c * (1 + (1 - x / c)^2) := by
    unfold invPoly3 invPoly1
    ring
  refine ⟨hp, ?_⟩
  calc invPoly1 x c = invPoly1 x c * 1 := by ring
       _ ≤ invPoly1 x c * (1 + (1 - x / c)^2) :=
         mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (1 - x / c)]) hp
       _ = invPoly3 x c := he.symm
       _ ≤ 1 / x := (invPoly3_midpoint x c hx hc hxc).2

#print axioms invPoly1_midpoint
#print axioms invPoly3_midpoint
#print axioms invPoly5_midpoint
#print axioms log_odd_seven_lower
end
end LeanLab.Languasco2004.Midpoint566
