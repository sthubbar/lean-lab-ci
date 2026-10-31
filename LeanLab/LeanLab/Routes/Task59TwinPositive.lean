/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Positivity of the constant in the U1451 singular series.
Source context: Matomaki and Merikoski, printed page 1, singular series display.
-/
import LeanLab.Routes.Task59TwinDefects

namespace LeanLab.Routes.Task59

/-- The twin constant in the MM14 transcription is strictly positive. -/
theorem twinProd_pos : 0 < LeanLab.Routes.U1451.twinProd := by
  have hf : ∀ p : {p : ℕ // p.Prime ∧ 2 < p},
      0 < 1 - (1 : ℝ) / ((p.1 : ℝ) - 1) ^ 2 := by
    intro p
    have hp : (2 : ℝ) < p.1 := by exact_mod_cast p.property.2
    have hpred : 0 < (p.1 : ℝ) - 1 := by linarith
    have hd : 0 < ((p.1 : ℝ) - 1) ^ 2 := pow_pos hpred _
    have hsq : 1 < ((p.1 : ℝ) - 1) ^ 2 := by nlinarith
    have hi : (1 : ℝ) / ((p.1 : ℝ) - 1) ^ 2 < 1 := (div_lt_one hd).mpr hsq
    linarith
  have hs : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      Real.log (1 - (1 : ℝ) / ((p.1 : ℝ) - 1) ^ 2)) := by
    simpa only [sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable summable_twin_defects.neg
  unfold LeanLab.Routes.U1451.twinProd
  rw [← Real.rexp_tsum_eq_tprod hf hs]
  exact Real.exp_pos _

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.twinProd_pos
