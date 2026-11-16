import LeanLab.ChenDoubleSieve.Task587FirstMoments

/-!
Reciprocal polynomial for D2,11 at row four of Wu 2004 Table 1 page 30.
Source: https://arxiv.org/abs/0705.1652, Lemma 5.2 page 26.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- Lower endpoints of row four D2,11. Wu 2004 page 26. -/
def r3ElevenLo : Fin 3 → ℝ := ![(25 / 89), (100 / 291), (100 / 291)]
/-- Upper endpoints of row four D2,11. Wu 2004 page 26. -/
def r3ElevenHi : Fin 3 → ℝ := ![(100 / 291), (2 / 5), (2 / 5)]
/-- Coordinate centers for the row four D2,11 polynomial. Wu 2004 page 26. -/
def r3ElevenCenter : Fin 3 → ℝ := ![(16175 / 51798), (541 / 1455), (541 / 1455)]
/-- Relative radii for the row four D2,11 polynomial. Wu 2004 page 26. -/
def r3ElevenRadius : Fin 3 → ℝ := ![(65 / 647), (41 / 541), (41 / 541)]
/-- Degree twelve reciprocal majorant for row four D2,11. Wu 2004 page 26. -/
def r3ElevenPoly (x : Fin 3 → ℝ) : ℝ :=
  (∏ j, reciprocalUpper 4 (r3ElevenCenter j) (r3ElevenRadius j) (x j)) *
    reciprocalUpper 4 (r3ElevenCenter 1) (r3ElevenRadius 1) (x 1)

/-- The explicit polynomial dominates the reciprocal kernel on D2,11.
Wu 2004 page 26, Table 1 row four page 30. -/
theorem r3Eleven_reciprocal_le_poly {x : Fin 3 → ℝ} (hx : x ∈ domain r3ElevenLo r3ElevenHi) :
    1 / ((∏ j, x j) * x 1) ≤ r3ElevenPoly x := by
  have hc (j : Fin 3) : 0 < r3ElevenCenter j := by fin_cases j <;> norm_num [r3ElevenCenter]
  have hrlt (j : Fin 3) : r3ElevenRadius j < 1 := by fin_cases j <;> norm_num [r3ElevenRadius]
  have hp (j : Fin 3) : 0 < x j := by
    have h := (hx.2 j).1
    fin_cases j <;> norm_num [r3ElevenLo] at h ⊢ <;> linarith
  have hr (j : Fin 3) : |1 - x j / r3ElevenCenter j| ≤ r3ElevenRadius j := by
    have hl := (hx.2 j).1
    have hu := (hx.2 j).2
    apply abs_le.mpr
    fin_cases j <;> norm_num [r3ElevenCenter, r3ElevenRadius, r3ElevenLo, r3ElevenHi] at hl hu ⊢ <;>
      constructor <;> linarith
  have h (j : Fin 3) := reciprocal_le_upper 4 (hc j) (hrlt j) (hr j)
  have hprod := prod_le_prod₀ (s := (univ : Finset (Fin 3)))
    (fun j _ => (one_div_pos.mpr (hp j)).le) (fun j _ => h j)
  calc
    1 / ((∏ j, x j) * x 1) = (∏ j, 1 / x j) * (1 / x 1) := by simp [mul_comm]
    _ ≤ r3ElevenPoly x := mul_le_mul hprod (h 1) (one_div_pos.mpr (hp 1)).le
      (prod_nonneg fun j _ => (one_div_pos.mpr (hp j)).le.trans (h j))

/-- The polynomial is integrable on the mixed ordered compact domain.
Wu 2004 page 26, derived quadrature preparation. -/
theorem r3ElevenPoly_integrable : IntegrableOn r3ElevenPoly (domain r3ElevenLo r3ElevenHi) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  unfold r3ElevenPoly reciprocalUpper
  fun_prop

end LeanLab.ChenDoubleSieve.Task587
