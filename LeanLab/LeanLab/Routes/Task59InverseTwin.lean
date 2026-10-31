/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The convergent reciprocal product named by the U1436 next action.
Source context: Matomaki and Merikoski, printed page 1, singular series display.
-/
import LeanLab.Routes.Task59TwinPositive
import LeanLab.Routes.Task59TwinFactor

namespace LeanLab.Routes.Task59

/-- The exact local factor product converges to the reciprocal twin constant. -/
theorem inverse_twin_hasProd :
    HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p.1 : ℝ) - 1) ^ 2 / ((p.1 : ℝ) * ((p.1 : ℝ) - 2)))
        LeanLab.Routes.U1451.twinProd⁻¹ := by
  have hm : Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      1 - (1 : ℝ) / ((p.1 : ℝ) - 1) ^ 2) := by
    simpa only [sub_eq_add_neg] using
      Real.multipliable_one_add_of_summable summable_twin_defects.neg
  have hh : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      1 - (1 : ℝ) / ((p.1 : ℝ) - 1) ^ 2) LeanLab.Routes.U1451.twinProd := hm.hasProd
  apply (hh.inv₀ twinProd_pos.ne').congr_fun
  intro p
  exact (twin_factor_inv_eq p.1 (by exact_mod_cast p.property.2)).symm

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.inverse_twin_hasProd
