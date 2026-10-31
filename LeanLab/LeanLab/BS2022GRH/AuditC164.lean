/- AI wrote the Lean code for CODEX task164.
Algebra audit of journal Lemma 14 p. 1237 and Theorem 7 p. 1235.
This records a QUESTION about the displayed proof, not a paper error finding.
Goldbach is open. -/
import Mathlib
import LeanLab.BS2022GRH.Constants
namespace LeanLab.BS2022GRH.AuditC164
/-- Normalizing the Lemma 14 bracket multiplies its short interval term by L.
Here L is log N, T is log of 8 over 3 plus 64 over L squared,
and h is the displayed short interval correction. -/
theorem normalization_difference (L C T h : ℝ) (hL : L ≠ 0) :
    L * (C / L + 36 / L ^ 3 + T * (h + 27 / L ^ 3)) -
      (C + 36 / L ^ 2 + T * (h + 27 / L ^ 2)) = T * h * (L - 1) := by
  field_simp
  <;> ring
/-- The two printed scalar brackets differ strictly when L exceeds one
and the short interval correction and its multiplier are positive. -/
theorem normalization_strict (L C T h : ℝ) (hL : 1 < L) (hT : 0 < T) (hh : 0 < h) :
    C + 36 / L ^ 2 + T * (h + 27 / L ^ 2) <
      L * (C / L + 36 / L ^ 3 + T * (h + 27 / L ^ 3)) := by
  have hd := normalization_difference L C T h (by linarith)
  have hp : 0 < T * h * (L - 1) := mul_pos (mul_pos hT hh) (by linarith)
  linarith
/-- The Lemma 14 scalar bound alone does not imply the printed normalized bound.
This statement concerns real bounds, without asserting anything about the actual prime count. -/
theorem scalar_bound_insufficient (L C T h : ℝ) (hL : 1 < L) (hT : 0 < T) (hh : 0 < h) :
    ∃ M : ℝ, M ≤ C / L + 36 / L ^ 3 + T * (h + 27 / L ^ 3) ∧
      C + 36 / L ^ 2 + T * (h + 27 / L ^ 2) < L * M := by
  exact ⟨_, le_rfl, normalization_strict L C T h hL hT hh⟩
/-- Concrete arithmetic instance of the strict scalar mismatch.
L = 100, C = 0.363084, T = 1 and h = 1e-12. -/
theorem scalar_instance :
    (0.363084 : ℝ) + 36 / 100 ^ 2 + (1e-12 + 27 / 100 ^ 2) <
      100 * (0.363084 / 100 + 36 / 100 ^ 3 + (1e-12 + 27 / 100 ^ 3)) := by
  norm_num
/-- The current lab sieve gives 8 R squared after Q = 2 R.
That scalar bound is strictly weaker than the paper's 4 R squared bound. -/
theorem large_sieve_constant_gap (X Y R : ℝ) (hX : 0 < X) (hY : 0 < Y) (hR : 0 < R) :
    Real.sqrt ((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R <
      Real.sqrt ((X + 8 * R ^ 2) * (Y + 8 * R ^ 2) * X * Y) / R := by
  apply (div_lt_div_iff_of_pos_right hR).mpr
  apply Real.sqrt_lt_sqrt (by positivity)
  have hr : 0 < R ^ 2 := sq_pos_of_pos hR
  gcongr <;> nlinarith
/-- Counting every integer is too weak for the endpoint progression estimate.
The explicit GRH error coefficient is already smaller than N at the standing threshold. -/
theorem trivial_count_too_weak :
    qG (4e18 : ℝ) * Real.sqrt (4e18 : ℝ) * Real.log (4e18 : ℝ) < 4e18 := by
  rw [sqrtX]
  calc qG (4e18 : ℝ) * 2e9 * Real.log (4e18 : ℝ)
      ≤ 0.6399 * 2e9 * 42.84 := by
        have hlog : 0 ≤ Real.log (4e18 : ℝ) := Real.log_nonneg (by norm_num)
        exact mul_le_mul (mul_le_mul_of_nonneg_right qG_le (by norm_num))
          logX_bounds.2 hlog (by norm_num)
    _ < _ := by norm_num
end LeanLab.BS2022GRH.AuditC164
#print axioms LeanLab.BS2022GRH.AuditC164.normalization_difference
#print axioms LeanLab.BS2022GRH.AuditC164.normalization_strict
#print axioms LeanLab.BS2022GRH.AuditC164.scalar_bound_insufficient
#print axioms LeanLab.BS2022GRH.AuditC164.scalar_instance
#print axioms LeanLab.BS2022GRH.AuditC164.large_sieve_constant_gap
#print axioms LeanLab.BS2022GRH.AuditC164.trivial_count_too_weak
