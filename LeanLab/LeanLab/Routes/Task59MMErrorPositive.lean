/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Positivity of the displayed MM14 error bracket is elementary.
Source: Matomaki and Merikoski, printed page 3, Theorem 1.4.
-/
import LeanLab.Routes.U1451MMSiegel

namespace LeanLab.Routes.Task59

open Real LeanLab.Routes.U1451

/-- The MM14 error bracket is positive on its arithmetic parameter range. -/
theorem mm14_error_pos (C ε η : ℝ) (q h : ℕ) (hq : 2 ≤ q) (hη : 10 ≤ η)
    (hh : (q : ℝ) ^ 10 ≤ h) : 0 < errTerm C ε η q h := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hh0 : (0 : ℝ) < h := lt_of_lt_of_le (pow_pos hq0 _) hh
  have hhN : 0 < h := by exact_mod_cast hh0
  have hφ : (0 : ℝ) < h.totient := by exact_mod_cast Nat.totient_pos.mpr hhN
  have hη0 : 0 < η := by linarith
  have hlogq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlogh : 0 ≤ log (h : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ h))
  have hV : 0 ≤ log (h : ℝ) / log q := div_nonneg hlogh hlogq.le
  unfold errTerm
  dsimp only
  positivity

example : 0 < errTerm 1 (1 / 10) 10 7 (2 * 7 ^ 10) :=
  mm14_error_pos _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.mm14_error_pos
