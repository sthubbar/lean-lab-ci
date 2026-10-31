/-
AI wrote this Lean code. Codex task69, 2026-10-25.
Concrete nonvacuity diagnostics for the new elementary interfaces.
These do not assert the sharp arc estimates for the actual prime sum.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.RangeError
import LeanLab.Zinoviev1997.PeriodArcs
import LeanLab.Zinoviev1997.MinorPointwise

namespace LeanLab.Zinoviev1997
open Real Finset LeanLab.HardyLittlewood1923.U1438

theorem large_odd_instance : Odd (10 ^ 20 + 1 : ℕ) ∧
    (10 : ℝ) ^ 20 ≤ ((10 ^ 20 + 1 : ℕ) : ℝ) := by
  norm_num [Odd]

theorem model_nine_positive : 0 < (modelIntegral 9).re := by
  rw [modelIntegral_nine, Complex.ofReal_re]
  positivity

theorem singular_nine_instance : SingularSeriesLower (sing3 9) :=
  singular_series_gt (by decide)

theorem lemma29_zero_instance : Lemma29At ((10 : ℝ) ^ 20) 3000 0 (0 : ℂ) := by
  constructor
  · intro _
    simp only [norm_zero]
    have hl : 0 ≤ Real.log ((10 : ℝ) ^ 20) := Real.log_nonneg (by norm_num)
    positivity
  · intro h
    norm_num at h

theorem loose_window_instance (t : ℝ) :
    ∀ α ∈ Set.Icc t (t + 1) \ majorArcs 9,
      ‖SZ 9 α‖ ≤ ∑' n, aZ 9 n := by
  intro α _
  exact norm_SZ_le (by norm_num : 0 < (9 : ℕ)) α

theorem zero_mem_majorArcs (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) :
    (0 : ℝ) ∈ majorArcs N := by
  have hq := arcCutoff_ge_2200 N hN
  have hl : 0 ≤ Real.log N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact Real.log_nonneg this
  simp only [majorArcs, Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨1, ?_, 0, by decide, by decide, 0, ?_⟩
  · simp only [Finset.mem_Icc]
    omega
  · simp only [Nat.cast_zero, zero_div, Int.cast_zero, add_zero, sub_zero, abs_zero]
    unfold arcRadius
    positivity

end LeanLab.Zinoviev1997
