import LeanLab.ChenDoubleSieve.Task587BoxMoments

/-!
Reciprocal polynomial for D2,13 at row four of Wu 2004 Table 1 page 30.
Source: https://arxiv.org/abs/0705.1652, Lemma 5.2 page 26.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- Lower endpoints of row four D2,13. Wu 2004 page 26. -/
def r3ThirteenLo : Fin 3 → ℝ := ![(25 / 103), (25 / 89), (100 / 291)]
/-- Upper endpoints of row four D2,13. Wu 2004 page 26. -/
def r3ThirteenHi : Fin 3 → ℝ := ![(25 / 89), (100 / 291), (2 / 5)]
/-- Coordinate centers for the row four D2,13 polynomial. Wu 2004 page 26. -/
def r3ThirteenCenter : Fin 3 → ℝ := ![(2400 / 9167), (16175 / 51798), (541 / 1455)]
/-- Relative radii for the row four D2,13 polynomial. Wu 2004 page 26. -/
def r3ThirteenRadius : Fin 3 → ℝ := ![(7 / 96), (65 / 647), (41 / 541)]
/-- Degree twenty reciprocal majorant for row four D2,13. Wu 2004 page 26. -/
def r3ThirteenPoly (x : Fin 3 → ℝ) : ℝ :=
  (∏ j, reciprocalUpper 6 (r3ThirteenCenter j) (r3ThirteenRadius j) (x j)) *
    reciprocalUpper 6 (r3ThirteenCenter 1) (r3ThirteenRadius 1) (x 1)

/-- The explicit polynomial dominates the reciprocal kernel on D2,13.
Wu 2004 page 26, Table 1 row four page 30. -/
theorem r3Thirteen_reciprocal_le_poly {x : Fin 3 → ℝ} (hx : x ∈ domain r3ThirteenLo r3ThirteenHi) :
    1 / ((∏ j, x j) * x 1) ≤ r3ThirteenPoly x := by
  have hc (j : Fin 3) : 0 < r3ThirteenCenter j := by fin_cases j <;> norm_num [r3ThirteenCenter]
  have hrlt (j : Fin 3) : r3ThirteenRadius j < 1 := by fin_cases j <;> norm_num [r3ThirteenRadius]
  have hp (j : Fin 3) : 0 < x j := by
    have h := (hx.2 j).1
    fin_cases j <;> norm_num [r3ThirteenLo] at h ⊢ <;> linarith
  have hr (j : Fin 3) : |1 - x j / r3ThirteenCenter j| ≤ r3ThirteenRadius j := by
    have hl := (hx.2 j).1
    have hu := (hx.2 j).2
    apply abs_le.mpr
    fin_cases j <;> norm_num [r3ThirteenCenter, r3ThirteenRadius, r3ThirteenLo, r3ThirteenHi] at hl hu ⊢ <;>
      constructor <;> linarith
  have h (j : Fin 3) := reciprocal_le_upper 6 (hc j) (hrlt j) (hr j)
  have hprod := prod_le_prod₀ (s := (univ : Finset (Fin 3)))
    (fun j _ => (one_div_pos.mpr (hp j)).le) (fun j _ => h j)
  calc
    1 / ((∏ j, x j) * x 1) = (∏ j, 1 / x j) * (1 / x 1) := by simp [mul_comm]
    _ ≤ r3ThirteenPoly x := mul_le_mul hprod (h 1) (one_div_pos.mpr (hp 1)).le
      (prod_nonneg fun j _ => (one_div_pos.mpr (hp j)).le.trans (h j))

/-- The polynomial is integrable on the mixed ordered compact domain.
Wu 2004 page 26, derived quadrature preparation. -/
theorem r3ThirteenPoly_integrable : IntegrableOn r3ThirteenPoly (domain r3ThirteenLo r3ThirteenHi) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  unfold r3ThirteenPoly reciprocalUpper
  fun_prop

/-- The three separated intervals make the ordered domain equal the full box.
Wu 2004 page 26, D2,13 at Table 1 row four page 30. -/
theorem r3Thirteen_domain_eq_box : domain r3ThirteenLo r3ThirteenHi = Set.Icc r3ThirteenLo r3ThirteenHi := by
  apply domain_eq_box_of_separated
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [r3ThirteenLo, r3ThirteenHi] <;> norm_num

end LeanLab.ChenDoubleSieve.Task587
