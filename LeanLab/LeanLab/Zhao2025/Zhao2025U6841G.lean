import Mathlib

/-!
# Zhao 2025, closed form of the Laplace transform `G` of (3.22)

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6841, CLOUD 20261021T0316Z-cloud57.
AI wrote the Lean code.  Binary Goldbach is open.

`g(u) = (2-u)³(4+6u+u²)/30 = -u⁵/30 + 2u³/3 - 4u²/3 + 16/15` on `[0, 2]`, the polynomial of
(3.21) as used by the lab numerics, and `G(z) = ∫₀² g(u) e^{-uz} du`.  For `z ≠ 0`,
`G(z) = 4(z+1)² e^{-2z}/z⁶ + 16/(15z) - 8/(3z³) + 4/z⁴ - 4/z⁶`, proved by an explicit
antiderivative.  This is the tool for certifying the Theorem I counts of (3.26).
-/

namespace LeanLab.Zhao2025.U6841

/-- The polynomial `g` of (3.21). -/
noncomputable def gpoly (u : ℝ) : ℝ := -u ^ 5 / 30 + 2 * u ^ 3 / 3 - 4 * u ^ 2 / 3 + 16 / 15

theorem gpoly_factored (u : ℝ) : gpoly u = (2 - u) ^ 3 * (4 + 6 * u + u ^ 2) / 30 := by
  unfold gpoly; ring

/-- `Q(u) = Σ_{j≤5} g⁽ʲ⁾(u)/z^{j+1}`. -/
noncomputable def Qz (z u : ℝ) : ℝ :=
  -u ^ 5 / (30 * z) - u ^ 4 / (6 * z ^ 2) + 2 * u ^ 3 / (3 * z) - 2 * u ^ 3 / (3 * z ^ 3)
    - 4 * u ^ 2 / (3 * z) + 2 * u ^ 2 / z ^ 2 - 2 * u ^ 2 / z ^ 4 - 8 * u / (3 * z ^ 2)
    + 4 * u / z ^ 3 - 4 * u / z ^ 5 + 16 / (15 * z) - 8 / (3 * z ^ 3) + 4 / z ^ 4 - 4 / z ^ 6

theorem hasDerivAt_A (z u : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun u => -(Real.exp (-(u * z)) * Qz z u))
      (gpoly u * Real.exp (-(u * z))) u := by
  have he : HasDerivAt (fun u => Real.exp (-(u * z))) (Real.exp (-(u * z)) * (-(1 * z))) u :=
    ((hasDerivAt_id u).mul_const z).neg.exp
  have hQ : HasDerivAt (fun u => Qz z u)
      (-(5 * u ^ 4) / (30 * z) - 4 * u ^ 3 / (6 * z ^ 2) + 2 * (3 * u ^ 2) / (3 * z)
        - 2 * (3 * u ^ 2) / (3 * z ^ 3) - 4 * (2 * u) / (3 * z) + 2 * (2 * u) / z ^ 2
        - 2 * (2 * u) / z ^ 4 - 8 / (3 * z ^ 2) + 4 / z ^ 3 - 4 / z ^ 5) u := by
    unfold Qz
    have p5 := hasDerivAt_pow 5 u
    have p4 := hasDerivAt_pow 4 u
    have p3 := hasDerivAt_pow 3 u
    have p2 := hasDerivAt_pow 2 u
    have p1 := hasDerivAt_id u
    have := ((((((((((((((p5.neg.div_const (30 * z)).sub (p4.div_const (6 * z ^ 2))).add
      ((p3.const_mul 2).div_const (3 * z))).sub ((p3.const_mul 2).div_const (3 * z ^ 3))).sub
      ((p2.const_mul 4).div_const (3 * z))).add ((p2.const_mul 2).div_const (z ^ 2))).sub
      ((p2.const_mul 2).div_const (z ^ 4))).sub ((p1.const_mul 8).div_const (3 * z ^ 2))).add
      ((p1.const_mul 4).div_const (z ^ 3))).sub ((p1.const_mul 4).div_const (z ^ 5))).add_const
      (16 / (15 * z))).sub_const (8 / (3 * z ^ 3))).add_const (4 / z ^ 4)).sub_const (4 / z ^ 6))
    convert this using 1
    · funext v; simp [id]
    · simp
  convert (he.mul hQ).neg using 1
  unfold gpoly Qz
  field_simp
  ring

/-- The closed form of `G(z) = ∫₀² g(u) e^{-uz} du` for `z ≠ 0`. -/
theorem G_closed (z : ℝ) (hz : z ≠ 0) :
    ∫ u in (0 : ℝ)..2, gpoly u * Real.exp (-(u * z)) =
      4 * (z + 1) ^ 2 * Real.exp (-(2 * z)) / z ^ 6 +
        (16 / (15 * z) - 8 / (3 * z ^ 3) + 4 / z ^ 4 - 4 / z ^ 6) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_A z u hz)]
  · unfold Qz
    simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    unfold gpoly; fun_prop

/-- `G(0) = ∫₀² g = 8/9`. -/
theorem G_zero : ∫ u in (0 : ℝ)..2, gpoly u * Real.exp (-(u * 0)) = 8 / 9 := by
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => -u ^ 6 / 180 + u ^ 4 / 6 - 4 * u ^ 3 / 9 + 16 * u / 15)
      (gpoly u) u := by
    intro u
    have := ((((hasDerivAt_pow 6 u).neg.div_const 180).add ((hasDerivAt_pow 4 u).div_const 6)).sub
      (((hasDerivAt_pow 3 u).const_mul 4).div_const 9)).add (((hasDerivAt_id u).const_mul 16).div_const 15)
    convert this using 1
    · funext v; simp [id]
    · unfold gpoly; simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)]
  · norm_num
  · apply Continuous.intervalIntegrable
    unfold gpoly; fun_prop

end LeanLab.Zhao2025.U6841

#print axioms LeanLab.Zhao2025.U6841.gpoly_factored
#print axioms LeanLab.Zhao2025.U6841.hasDerivAt_A
#print axioms LeanLab.Zhao2025.U6841.G_closed
#print axioms LeanLab.Zhao2025.U6841.G_zero
