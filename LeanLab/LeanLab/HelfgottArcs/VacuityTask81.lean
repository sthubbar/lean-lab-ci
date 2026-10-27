/-
Concrete parameter and derivative instances for CODEX task81.
The cited analytic inputs in conditional theorems are not discharged here.
Sources and plain math twins are in STATEMENTS.md.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.MajorAssembly
import LeanLab.HelfgottArcs.MajorParameters
import LeanLab.HelfgottArcs.FiniteSAudit
import LeanLab.HelfgottArcs.FourierDecay
import LeanLab.HelfgottArcs.MellinHalf

namespace LeanLab.HelfgottArcs
open Real MeasureTheory Set

example : (1 : DirichletCharacter ℂ 1).IsPrimitive :=
  DirichletCharacter.isPrimitive_one_level_one

example := gaussian_error_terms_le (q := 1) (x := 10 ^ 8) (by norm_num) (by norm_num)
example := gaussian_explicit_error_le (q := 1) (d := 0) (x := 10 ^ 8)
  (u := 1000 / (12 * π)) (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) le_rfl
example := t2_corrected_sqrt_terms_le (q := 1) (by norm_num) (by norm_num)
example := t2_corrected_error_terms_le (q := 1) (d := 0) (x := 10 ^ 8)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example := convolution_corrected_sqrt_terms_le (q := 1) (by norm_num) (by norm_num)
example := convolution_corrected_error_terms_le (q := 1) (d := 0) (x := 10 ^ 8)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example := etaPlus_error_terms_le (q := 1) (x := 10 ^ 12) (by norm_num) (by norm_num)
example := etaPlus_q1_error_terms_le (x := 10 ^ 12) (by norm_num)

example := gaussian_height_bounds (q := 1) (δ := 0)
  (by norm_num) (by norm_num) (by norm_num)
example := gaussian_height_bounds (q := 1) (δ := 1)
  (by norm_num) (by norm_num) (by norm_num)
example := etaPlus_height_within_verification 1 (Or.inl ⟨by decide, by decide⟩)
example := etaPlus_height_within_verification 2 (Or.inr ⟨by decide, by decide⟩)
example := etaPlus_q1_height_bounds (δ := 0) (by norm_num)
example := etaPlus_q1_height_bounds (δ := 1) (by norm_num)

example := S_eta2_eq_sum 0 8 (by norm_num)
example := norm_S_eta2_le_sum 0 8 (by norm_num)
example := norm_S_eta2_le_coarse 0 8 (by norm_num)
example := minorBoundLarge_x0_lt_x0
example := coarse_bound_exceeds_minor_at_x0

example := hasDerivAt_e_neg_mul 1 0
example := interval_fourier_parts 0 1 1 (fun t : ℝ => t) (fun _ => 1)
  continuous_id.continuousOn continuous_const.continuousOn (fun t _ => hasDerivAt_id' t)
example := norm_interval_fourier_le 0 1 0 (by norm_num) (fun _ => 1)
example := norm_interval_fourier_mul_le 0 1 1 (by norm_num)
  (fun t : ℝ => t) (fun _ => 1) continuous_id.continuousOn continuous_const.continuousOn
  (fun t _ => hasDerivAt_id' t)
example := mul_fhat_eta2_eq 1
example := norm_fhat_eta2_le_inv (δ := 1) (by norm_num)
example := sq_mul_fhat_eta2_eq 1
example := norm_eta2_smooth_fourier_le (δ := 1) (by norm_num)
example := norm_second_fourier_eta2_le_of_large (δ := 655) (by norm_num)
example := mul_fhat_eta2rho_eq 4 1 (by norm_num)
example := norm_fhat_eta2rho_lt_inv (ρ := 4) (δ := 1) (by norm_num) (by norm_num)

/-- A single compact frequency sample is elementary. The full interval input is separate. -/
example : ‖(-2 * π * Complex.I * (0 : ℂ)) ^ 2 * fhat eta2 0‖ ≤ 31.521 := by norm_num

example := fhat_neg_eq_conj eta2 1
example := a2_interpolation_rounding
example := integral_eta2_div_sqrt
example := mellin_half_eta2_le

end LeanLab.HelfgottArcs
