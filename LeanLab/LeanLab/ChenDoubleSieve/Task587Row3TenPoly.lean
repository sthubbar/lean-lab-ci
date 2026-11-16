import LeanLab.ChenDoubleSieve.Task587MixedMoments

/-!
Reciprocal polynomial for D2,10 at row four of Wu 2004 Table 1 page 30.
Source: https://arxiv.org/abs/0705.1652, Lemma 5.2 page 26.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- Lower endpoints of row four D2,10. Wu 2004 page 26. -/
def r3TenLo : Fin 3 → ℝ := ![25 / 89, 25 / 89, 100 / 291]
/-- Upper endpoints of row four D2,10. Wu 2004 page 26. -/
def r3TenHi : Fin 3 → ℝ := ![100 / 291, 100 / 291, 2 / 5]
/-- Coordinate centers for the row four D2,10 polynomial. Wu 2004 page 26. -/
def r3TenCenter : Fin 3 → ℝ := ![16175 / 51798, 16175 / 51798, 541 / 1455]
/-- Relative radii for the row four D2,10 polynomial. Wu 2004 page 26. -/
def r3TenRadius : Fin 3 → ℝ := ![65 / 647, 65 / 647, 41 / 541]
/-- Degree twelve reciprocal majorant for row four D2,10. Wu 2004 page 26. -/
def r3TenPoly (x : Fin 3 → ℝ) : ℝ :=
  (∏ j, reciprocalUpper 4 (r3TenCenter j) (r3TenRadius j) (x j)) *
    reciprocalUpper 4 (r3TenCenter 1) (r3TenRadius 1) (x 1)

/-- The explicit polynomial dominates the reciprocal kernel on D2,10.
Wu 2004 page 26, Table 1 row four page 30. -/
theorem r3Ten_reciprocal_le_poly {x : Fin 3 → ℝ} (hx : x ∈ domain r3TenLo r3TenHi) :
    1 / ((∏ j, x j) * x 1) ≤ r3TenPoly x := by
  have hc (j : Fin 3) : 0 < r3TenCenter j := by fin_cases j <;> norm_num [r3TenCenter]
  have hrlt (j : Fin 3) : r3TenRadius j < 1 := by fin_cases j <;> norm_num [r3TenRadius]
  have hp (j : Fin 3) : 0 < x j := by
    have h := (hx.2 j).1
    fin_cases j <;> norm_num [r3TenLo] at h ⊢ <;> linarith
  have hr (j : Fin 3) : |1 - x j / r3TenCenter j| ≤ r3TenRadius j := by
    have hl := (hx.2 j).1
    have hu := (hx.2 j).2
    apply abs_le.mpr
    fin_cases j <;> norm_num [r3TenCenter, r3TenRadius, r3TenLo, r3TenHi] at hl hu ⊢ <;>
      constructor <;> linarith
  have h (j : Fin 3) := reciprocal_le_upper 4 (hc j) (hrlt j) (hr j)
  have hprod := prod_le_prod₀ (s := (univ : Finset (Fin 3)))
    (fun j _ => (one_div_pos.mpr (hp j)).le) (fun j _ => h j)
  calc
    1 / ((∏ j, x j) * x 1) = (∏ j, 1 / x j) * (1 / x 1) := by simp [mul_comm]
    _ ≤ r3TenPoly x := mul_le_mul hprod (h 1) (one_div_pos.mpr (hp 1)).le
      (prod_nonneg fun j _ => (one_div_pos.mpr (hp j)).le.trans (h j))

/-- The polynomial is integrable on the mixed ordered compact domain.
Wu 2004 page 26, derived quadrature preparation. -/
theorem r3TenPoly_integrable : IntegrableOn r3TenPoly (domain r3TenLo r3TenHi) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  unfold r3TenPoly reciprocalUpper
  fun_prop

end LeanLab.ChenDoubleSieve.Task587
