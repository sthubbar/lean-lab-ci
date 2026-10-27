import LeanLab.Zhao2025.BMonotone
import LeanLab.Zhao2025.LaplaceOrder

/-!
The positive Laplace representation behind Lemma 2.3.
Source: Zhao 2025, displays 2.15 and 2.22, pages 5 and 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The Laplace representation split at t. -/
noncomputable def BLaplace (t l l0 : ℝ) : ℝ :=
  1 / 6 * (∫ u in 0..(2 * t), Real.exp (-(l + l0) * u)) +
    1 / l0 * ((∫ u in 0..t, (1 - Real.exp (-l0 * u)) * Real.exp (-l * u)) +
      ∫ u in t..(2 * t),
        (Real.exp (-(2 * l0 * (u - t))) - Real.exp (-l0 * u)) * Real.exp (-l * u))

/-- The printed rational expression equals its integral representation for positive parameters. -/
theorem B_eq_laplace (t l l0 : ℝ) (hl : 0 < l) (h0 : 0 < l0) :
    B t l l0 = BLaplace t l l0 := by
  have h1 (u : ℝ) : (1 - Real.exp (-l0 * u)) * Real.exp (-l * u) =
      Real.exp (-l * u) - Real.exp (-(l + l0) * u) := by
    rw [sub_mul, one_mul, ← Real.exp_add]
    congr 1
    congr 1
    ring
  have h2 (u : ℝ) :
      (Real.exp (-(2 * l0 * (u - t))) - Real.exp (-l0 * u)) * Real.exp (-l * u) =
      Real.exp (2 * l0 * t) * Real.exp (-(l + 2 * l0) * u) -
        Real.exp (-(l + l0) * u) := by
    rw [sub_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  have hi (c a b : ℝ) : IntervalIntegrable (fun u : ℝ => Real.exp (c * u))
      MeasureTheory.volume a b := (by fun_prop : Continuous _).intervalIntegrable a b
  have hn : l ≠ 0 := ne_of_gt hl
  have hn0 : l0 ≠ 0 := ne_of_gt h0
  have hns : l + l0 ≠ 0 := ne_of_gt (add_pos hl h0)
  have hn2 : l + 2 * l0 ≠ 0 := by positivity
  have hprod : Real.exp (2 * l0 * t) *
      (Real.exp (-(l + 2 * l0) * (2 * t)) - Real.exp (-(l + 2 * l0) * t)) =
      Real.exp (-(l + l0) * (2 * t)) - Real.exp (-l * t) := by
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  unfold BLaplace
  simp_rw [h1, h2]
  rw [intervalIntegral.integral_sub (hi (-l) 0 t) (hi (-(l + l0)) 0 t),
    intervalIntegral.integral_sub
      ((hi (-(l + 2 * l0)) t (2 * t)).const_mul (Real.exp (2 * l0 * t)))
      (hi (-(l + l0)) t (2 * t)), intervalIntegral.integral_const_mul]
  rw [exp_integral 0 (2 * t) (-(l + l0)) (neg_ne_zero.mpr hns),
    exp_integral 0 t (-l) (neg_ne_zero.mpr hn),
    exp_integral 0 t (-(l + l0)) (neg_ne_zero.mpr hns),
    exp_integral t (2 * t) (-(l + 2 * l0)) (neg_ne_zero.mpr hn2),
    exp_integral t (2 * t) (-(l + l0)) (neg_ne_zero.mpr hns)]
  rw [← mul_div_assoc (Real.exp (2 * l0 * t))
    (Real.exp (-(l + 2 * l0) * (2 * t)) - Real.exp (-(l + 2 * l0) * t))
    (-(l + 2 * l0)), hprod]
  have hF : Real.exp (-(l + l0) * (2 * t)) = Real.exp (-(2 * (l + l0) * t)) := by
    congr 1
    ring
  have hE : Real.exp (-l * t) = Real.exp (-(l * t)) := by
    congr 1
    ring
  rw [hF, hE]
  unfold B
  simp only [mul_zero, Real.exp_zero]
  field_simp [hn, hn0, hns, hn2]
  <;> ring

#print axioms B_eq_laplace

end LeanLab.Zhao2025.Task56
