/- AI wrote this Lean code for CODEX task700. Goldbach is open.
A counterexample to the existing lab real CDEM leaf.
This is the real statement in Lemma5MuS63. The corrected integer source statement is a separate leaf.
The recorded example is from the S63 source audit of 2026-11-22.
-/
import LeanLab.BS2022GRH.FiniteCount700
import LeanLab.BS2022GRH.Witness700Counterexample

namespace LeanLab.BS2022GRH.FalseCdem700
open Real Finset Witness700 SquarefreeSound700
noncomputable section

/-- The certified upper count at the integer endpoint of the recorded counterexample. -/
theorem count_endpoint : sqCount 441352 ≤ 268292 := by
  exact (verify_sound counterexampleRows 438652 266651 441352 268292
    FiniteCount700.certified_count_endpoint counterexample_cert).1

/-- The literal real argument in the recorded lab counterexample violates the sharp error. -/
theorem cdem07_real_counterexample :
    0.02767*√(44135299/100 : ℝ) <
      |(sqCount 441352 : ℝ)-6/π^2*(44135299/100 : ℝ)| := by
  let q : ℝ := sqCount 441352
  change 0.02767*√(44135299/100 : ℝ) < |q-6/π^2*(44135299/100 : ℝ)|
  have hq : q ≤ 268292 := by
    change (sqCount 441352 : ℝ) ≤ 268292
    exact_mod_cast count_endpoint
  have hp : π ≤ (3.1415926536 : ℝ) := pi_lt_d20.le.trans (by norm_num)
  have hp2 := pow_le_pow_left₀ pi_pos.le hp 2
  have hc : (0.6079271018 : ℝ) ≤ 6/π^2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hs : √(44135299/100 : ℝ) ≤ 664.345 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num
  have hprod := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ 44135299/100 by norm_num)
  have ha := neg_le_abs (q-6/π^2*(44135299/100 : ℝ))
  linarith

/-- The real statement of the existing lab CDEM leaf is false. -/
theorem not_cdem07_thm3_real :
    ¬ (∀ x : ℝ, 438653 ≤ x →
      |(((Icc 1 ⌊x⌋₊).filter (fun n => Squarefree n)).card : ℝ)-6/π^2*x|
        ≤ 0.02767*√x) := by
  intro h
  have hh := h (44135299/100) (by norm_num)
  have hf : ⌊(44135299/100 : ℝ)⌋₊ = 441352 := by norm_num
  rw [hf] at hh
  have hc := cdem07_real_counterexample
  change 0.02767*√(44135299/100 : ℝ) <
    |(((Icc 1 441352).filter (fun n => Squarefree n)).card : ℝ)-
      6/π^2*(44135299/100 : ℝ)| at hc
  exact (not_lt_of_ge hh) hc

end
end LeanLab.BS2022GRH.FalseCdem700

#print axioms LeanLab.BS2022GRH.FalseCdem700.count_endpoint
#print axioms LeanLab.BS2022GRH.FalseCdem700.cdem07_real_counterexample
#print axioms LeanLab.BS2022GRH.FalseCdem700.not_cdem07_thm3_real
