import LeanLab.ChirreHagen2025.Statements

/-!
P0075 page 4, equation 2.6.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.MeanSquare122
open MeasureTheory

/-- P0075 page 4, equation 2.6, for square-integrable complex functions. -/
theorem equation2_6 (a b η : ℝ) (hab : a ≤ b) (hη : 0 < η) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a b))) :
    (∫ x in a..b, ‖f x + g x‖ ^ 2) ≤
      (1 + η) * (∫ x in a..b, ‖f x‖ ^ 2) +
        (1 + 1 / η) * (∫ x in a..b, ‖g x‖ ^ 2) := by
  have hfi : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (hf.integrable_norm_pow (by norm_num))
  have hgi : IntervalIntegrable (fun x => ‖g x‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (hg.integrable_norm_pow (by norm_num))
  have hfgi : IntervalIntegrable (fun x => ‖f x + g x‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      ((hf.add hg).integrable_norm_pow (by norm_num))
  have hright := (hfi.const_mul (1 + η)).add (hgi.const_mul (1 + 1 / η))
  calc
    _ ≤ ∫ x in a..b, ((1 + η) * ‖f x‖ ^ 2 + (1 + 1 / η) * ‖g x‖ ^ 2) := by
      apply intervalIntegral.integral_mono hab hfgi hright
      intro x
      have htri := pow_le_pow_left₀ (norm_nonneg (f x + g x)) (norm_add_le (f x) (g x)) 2
      have hy := two_mul_le_add_mul_sq (a := ‖f x‖) (b := ‖g x‖) hη
      simp only [one_div] at *
      nlinarith
    _ = _ := by
      rw [intervalIntegral.integral_add (hfi.const_mul _) (hgi.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end LeanLab.ChirreHagen2025.MeanSquare122
