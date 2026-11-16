import LeanLab.ChenDoubleSieve.Task587PolynomialTools

/-!
Reciprocal polynomial for D2,9 at row four of Wu 2004 Table 1 page 30.
Source: https://arxiv.org/abs/0705.1652, Lemma 5.2 page 26.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- Degree twenty polynomial majorant for the row four D2,9 reciprocal kernel.
Wu 2004 page 26, derived six-term enclosure with radius 53/303. -/
def r3NinePoly (x : Fin 3 → ℝ) : ℝ :=
  (∏ j, reciprocalUpper 6 (303 / 890) (53 / 303) (x j)) *
    reciprocalUpper 6 (303 / 890) (53 / 303) (x 1)

/-- The explicit polynomial bounds the entire reciprocal kernel.
Wu 2004 page 26, D2,9 at Table 1 row four. -/
theorem r3Nine_reciprocal_le_poly {x : Fin 3 → ℝ}
    (hx : x ∈ domain (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ))) :
    Wu04I1.reciprocal x ≤ r3NinePoly x := by
  have hp (j : Fin 3) : 0 < x j := lt_of_lt_of_le (by norm_num) (hx.2 j).1
  have hr (j : Fin 3) : |1 - x j / (303 / 890 : ℝ)| ≤ (53 / 303 : ℝ) := by
    apply abs_le.mpr
    constructor <;> norm_num <;> linarith [(hx.2 j).1, (hx.2 j).2]
  have h (j : Fin 3) := reciprocal_le_upper 6 (by norm_num : (0 : ℝ) < 303 / 890)
    (by norm_num : (53 / 303 : ℝ) < 1) (hr j)
  have hprod := prod_le_prod₀ (s := (univ : Finset (Fin 3)))
    (fun j _ => (one_div_pos.mpr (hp j)).le) (fun j _ => h j)
  calc
    Wu04I1.reciprocal x = (∏ j, 1 / x j) * (1 / x 1) := by
      simp [Wu04I1.reciprocal, mul_comm]
    _ ≤ r3NinePoly x := mul_le_mul hprod (h 1) (one_div_pos.mpr (hp 1)).le
      (prod_nonneg fun j _ => (one_div_pos.mpr (hp j)).le.trans (h j))

/-- The reciprocal polynomial is integrable on the ordered compact chamber.
Wu 2004 page 26, derived exact quadrature preparation. -/
theorem r3NinePoly_integrable : IntegrableOn r3NinePoly
    (domain (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ))) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  unfold r3NinePoly reciprocalUpper
  fun_prop

/-- The reciprocal integral is bounded by the polynomial integral.
Wu 2004 page 26, derived rational certificate reduction. -/
theorem r3Nine_integral_le_poly :
    (∫ x in domain (fun _ : Fin 3 => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)),
      Wu04I1.reciprocal x) ≤
    (∫ x in domain (fun _ : Fin 3 => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)),
      r3NinePoly x) := by
  have hi := Wu04I1.reciprocal_integrable (s := (5 / 2 : ℝ))
    (by norm_num : (0 : ℝ) < 89 / 25)
  norm_num at hi
  exact setIntegral_mono_on hi r3NinePoly_integrable
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => r3Nine_reciprocal_le_poly hx)

end LeanLab.ChenDoubleSieve.Task587
