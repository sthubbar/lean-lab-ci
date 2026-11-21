import LeanLab.LiuWang2002.ThetaCert352

/-!
A negative comparison for the attempted analytic replacement of a finite certificate.
Source Schoenfeld 1976 page 356, display 5.1 star.
This states a gap between scalar upper bounds. It asserts no paper error.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task667

/-- The printed theta coefficient alone does not imply the stronger
logarithmic coefficient required by primorial n times 25 to power n below 68 to power n. -/
theorem printed_theta_envelope_insufficient :
    ¬ (∀ T : ℝ, 0 ≤ T → T < 1.001093 → T < Real.log (68 / 25 : ℝ)) := by
  have hgap : Real.log (68 / 25 : ℝ) < 1.001093 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 68 / 25)).mpr
      Task352.certificate_base
  have hlog : 0 ≤ Real.log (68 / 25 : ℝ) := Real.log_nonneg (by norm_num)
  intro h
  have hbad := h ((Real.log (68 / 25 : ℝ) + 1.001093) / 2) (by linarith) (by linarith)
  linarith

end LeanLab.LiuWang2002.Task667
#print axioms LeanLab.LiuWang2002.Task667.printed_theta_envelope_insufficient
