/-
P0076 Definition 6.3. Logarithm tangent bounds for the right integral.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.SieveIntegrals

open MeasureTheory intervalIntegral Set

namespace LeanLab.Teravainen2016

noncomputable def invQuadPrimitive (u : ℝ) : ℝ :=
  (Real.log (1 + u) - Real.log (1 - u)) / 2

noncomputable def sieveTangent (L u : ℝ) : ℝ :=
  (120 / 37) / L + (Real.log L - 1 - 1 / L) / (1 - u ^ 2)

noncomputable def sieveRightIntegrand (u : ℝ) : ℝ :=
  Real.log ((120 / 37) * (1 - u ^ 2) - 1) / (1 - u ^ 2)

/-- The logarithmic primitive of inverse one minus u squared. -/
theorem hasDerivAt_invQuadPrimitive {u : ℝ} (hlo : -1 < u) (hhi : u < 1) :
    HasDerivAt invQuadPrimitive (1 / (1 - u ^ 2)) u := by
  have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + u)) u := by
    simpa using ((hasDerivAt_id u).const_add 1).log (by linarith : 1 + u ≠ 0)
  have h2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - u)) u := by
    simpa using ((hasDerivAt_const u 1).sub (hasDerivAt_id u)).log (by linarith : 1 - u ≠ 0)
  convert (h1.sub h2).div_const 2 using 1
  · rfl
  · have hp : 1 + u ≠ 0 := by linarith
    have hm : 1 - u ≠ 0 := by linarith
    have hd : 1 - u ^ 2 ≠ 0 := by
      rw [show 1 - u ^ 2 = (1 - u) * (1 + u) by ring]
      exact mul_ne_zero hm hp
    field_simp [hp, hm, hd]
    ring

/-- Difference of the logarithmic primitive at two points. -/
theorem invQuadPrimitive_sub {a b : ℝ} (ha0 : -1 < a) (ha1 : a < 1)
    (hb0 : -1 < b) (hb1 : b < 1) :
    invQuadPrimitive b - invQuadPrimitive a =
      Real.log (((1 + b) * (1 - a)) / ((1 - b) * (1 + a))) / 2 := by
  unfold invQuadPrimitive
  have haP : 0 < 1 + a := by linarith
  have haM : 0 < 1 - a := by linarith
  have hbP : 0 < 1 + b := by linarith
  have hbM : 0 < 1 - b := by linarith
  rw [Real.log_div (mul_pos hbP haM).ne' (mul_pos hbM haP).ne',
    Real.log_mul hbP.ne' haM.ne', Real.log_mul hbM.ne' haP.ne']
  ring

/-- A tangent segment has the closed value used in the margin certificate. -/
theorem integral_sieveTangent (L : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (∫ u in a..b, sieveTangent L u) =
      sieveTangentTerm L (b - a) (((1 + b) * (1 - a)) / ((1 - b) * (1 + a))) := by
  let c := Real.log L - 1 - 1 / L
  have hden : ∀ u ∈ Icc a b, 1 - u ^ 2 ≠ 0 := by
    intro u hu
    have hu0 : 0 ≤ u := ha.trans hu.1
    have hu1 : u < 1 := hu.2.trans_lt hb
    nlinarith
  have hc : ContinuousOn (fun u : ℝ => 1 - u ^ 2) (Icc a b) := by fun_prop
  have hint : IntervalIntegrable (sieveTangent L) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have hh : ContinuousOn (fun u : ℝ => (120 / 37) / L + c * (1 - u ^ 2)⁻¹) (Icc a b) :=
      continuousOn_const.add (continuousOn_const.mul (hc.inv₀ hden))
    unfold sieveTangent
    simpa [c, div_eq_mul_inv] using hh
  have hder : ∀ u ∈ uIcc a b,
      HasDerivAt (fun u : ℝ => (120 / 37) / L * u + c * invQuadPrimitive u)
        (sieveTangent L u) u := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    have hu0 : -1 < u := by linarith [hu.1]
    have hu1 : u < 1 := hu.2.trans_lt hb
    have hp := (hasDerivAt_invQuadPrimitive hu0 hu1).const_mul c
    have hlin := (hasDerivAt_id u).const_mul ((120 / 37) / L)
    convert hlin.add hp using 1
    · rfl
    · simp [sieveTangent, c, div_eq_mul_inv]
  have he := integral_eq_sub_of_hasDerivAt hder hint
  rw [show ((120 / 37 : ℝ) / L * b + c * invQuadPrimitive b) -
      ((120 / 37) / L * a + c * invQuadPrimitive a) =
      (120 / 37) / L * (b - a) + c * (invQuadPrimitive b - invQuadPrimitive a) by ring,
    invQuadPrimitive_sub (by linarith) (lt_of_le_of_lt hab hb) (by linarith) hb] at he
  exact he

/-- The tangent line inequality for log gives a pointwise majorant. -/
theorem sieveRightIntegrand_le_tangent {L u : ℝ} (hL : 0 < L)
    (hu : 0 ≤ u) (hu1 : u ≤ 31 / 50) :
    sieveRightIntegrand u ≤ sieveTangent L u := by
  have hd : 0 < 1 - u ^ 2 := by nlinarith
  have hy : 0 < (120 / 37 : ℝ) * (1 - u ^ 2) - 1 := by nlinarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hy hL)
  rw [Real.log_div hy.ne' hL.ne'] at hlog
  unfold sieveRightIntegrand sieveTangent
  rw [div_le_iff₀ hd]
  have he : ((120 / 37) / L + (Real.log L - 1 - 1 / L) / (1 - u ^ 2)) * (1 - u ^ 2) =
      Real.log L + (((120 / 37) * (1 - u ^ 2) - 1) / L - 1) := by
    field_simp
    ring
  rw [he]
  linarith

#print axioms hasDerivAt_invQuadPrimitive
#print axioms invQuadPrimitive_sub
#print axioms integral_sieveTangent
#print axioms sieveRightIntegrand_le_tangent

end LeanLab.Teravainen2016
