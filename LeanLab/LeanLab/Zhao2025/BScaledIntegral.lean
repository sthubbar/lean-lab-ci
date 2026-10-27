import LeanLab.Zhao2025.ExpPairIntegral
import LeanLab.Zhao2025.BIntegral

/-!
The scaled positive lambda0 branch in the proof of Lemma 2.3.
Source: Zhao 2025, displays 2.20 and 2.23, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The symmetric integral for exp of lambda t times B. -/
noncomputable def BScaled (t l l0 : ℝ) : ℝ :=
  1 / 6 * (Real.exp (-l0 * t) *
    ∫ u in 0..t, Real.exp ((l + l0) * u) + Real.exp (-(l + l0) * u)) +
    1 / l0 * ∫ u in 0..t, (1 - Real.exp (-l0 * (t - u))) *
      (Real.exp (l * u) + Real.exp (-(l + 2 * l0) * u))

/-- The printed B formula has the scaled integral representation of display 2.23. -/
theorem B_scaled_eq (t l l0 : ℝ) (hl : 0 < l) (h0 : 0 < l0) :
    Real.exp (l * t) * B t l l0 = BScaled t l l0 := by
  have hn : l ≠ 0 := ne_of_gt hl
  have hn0 : l0 ≠ 0 := ne_of_gt h0
  have hns : l + l0 ≠ 0 := ne_of_gt (add_pos hl h0)
  have hn2 : l + 2 * l0 ≠ 0 := by positivity
  have hi (c : ℝ) : IntervalIntegrable (fun u : ℝ => Real.exp (c * u))
      MeasureTheory.volume 0 t := (by fun_prop : Continuous _).intervalIntegrable 0 t
  have hprod : Real.exp (-l0 * t) *
      (Real.exp ((l + l0) * t) - Real.exp (-(l + l0) * t)) =
      Real.exp (l * t) - Real.exp (-(l + 2 * l0) * t) := by
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  have hpc : Real.exp (-l0 * t) *
      (∫ u in 0..t, Real.exp ((l + l0) * u) + Real.exp (-(l + l0) * u)) =
      (Real.exp (l * t) - Real.exp (-(l + 2 * l0) * t)) / (l + l0) := by
    rw [exp_pair_integral t (l + l0) hns, ← mul_div_assoc, hprod]
  have hexpand (u : ℝ) :
      (1 - Real.exp (-l0 * (t - u))) *
          (Real.exp (l * u) + Real.exp (-(l + 2 * l0) * u)) =
        (Real.exp (l * u) + Real.exp (-(l + 2 * l0) * u)) -
          Real.exp (-l0 * t) * (Real.exp ((l + l0) * u) + Real.exp (-(l + l0) * u)) := by
    have h1 : Real.exp (-l0 * (t - u)) * Real.exp (l * u) =
        Real.exp (-l0 * t) * Real.exp ((l + l0) * u) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-l0 * (t - u)) * Real.exp (-(l + 2 * l0) * u) =
        Real.exp (-l0 * t) * Real.exp (-(l + l0) * u) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [sub_mul, one_mul, mul_add, mul_add, h1, h2]
  have hg : (∫ u in 0..t, (1 - Real.exp (-l0 * (t - u))) *
        (Real.exp (l * u) + Real.exp (-(l + 2 * l0) * u))) =
      (Real.exp (l * t) - 1) / l +
        (Real.exp (-(l + 2 * l0) * t) - 1) / (-(l + 2 * l0)) -
        (Real.exp (l * t) - Real.exp (-(l + 2 * l0) * t)) / (l + l0) := by
    simp_rw [hexpand]
    rw [intervalIntegral.integral_sub ((hi l).add (hi (-(l + 2 * l0))))
      (((hi (l + l0)).add (hi (-(l + l0)))).const_mul (Real.exp (-l0 * t))),
      intervalIntegral.integral_const_mul, hpc,
      intervalIntegral.integral_add (hi l) (hi (-(l + 2 * l0))),
      exp_integral 0 t l hn, exp_integral 0 t (-(l + 2 * l0)) (neg_ne_zero.mpr hn2)]
    simp only [mul_zero, Real.exp_zero]
  have he0 : Real.exp (l * t) * Real.exp (-(l * t)) = 1 := by
    rw [← Real.exp_add, show l * t + -(l * t) = 0 by ring, Real.exp_zero]
  have he2 : Real.exp (l * t) * Real.exp (-(2 * (l + l0) * t)) =
      Real.exp (-(l + 2 * l0) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : Real.exp (l * t) * B t l l0 =
      1 / 6 * ((Real.exp (l * t) - Real.exp (-(l + 2 * l0) * t)) / (l + l0)) +
        (Real.exp (l * t) - 1) / (l * (l + l0)) +
        (Real.exp (-(l + 2 * l0) * t) - 1) / ((l + l0) * (l + 2 * l0)) := by
    unfold B
    calc
      _ = 1 / 6 * ((Real.exp (l * t) -
            Real.exp (l * t) * Real.exp (-(2 * (l + l0) * t))) / (l + l0)) +
          (Real.exp (l * t) - Real.exp (l * t) * Real.exp (-(l * t))) / (l * (l + l0)) +
          (Real.exp (l * t) * Real.exp (-(2 * (l + l0) * t)) -
            Real.exp (l * t) * Real.exp (-(l * t))) / ((l + l0) * (l + 2 * l0)) := by ring
      _ = _ := by simp only [he0, he2]
  rw [hs]
  unfold BScaled
  rw [hpc, hg]
  field_simp [hn, hn0, hns, hn2]
  <;> ring

#print axioms B_scaled_eq

end LeanLab.Zhao2025.Task56
