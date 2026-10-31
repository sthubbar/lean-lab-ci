/-
AI wrote this Lean code for CODEX task51.
P0074 page 11, the unscaled Type I estimate with explicit constant fifty.
This does not include the beta-sieve normalization factor.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.TypeILogLength

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The logarithmic factor is at most twice the logarithm printed in the paper. -/
theorem typeI_log_scale {q : ℕ} (hq : 0 < q) {H : ℝ} (hH : 1 ≤ H) :
    1 + Real.log q + Real.log H ≤ 2 * Real.log (2 * (q : ℝ) * H) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqR : (0 : ℝ) < q := by linarith
  have hHR : 0 < H := by linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  rw [Real.log_mul (mul_ne_zero (by norm_num) hqR.ne') hHR.ne',
    Real.log_mul (by norm_num) hqR.ne']
  linarith

/-- The unscaled Type I estimate on page 11 holds with absolute constant fifty for H at least one. -/
theorem divisorWeight_paper_log_le {q : ℕ} (hq : 0 < q) {r : ℤ}
    (hr : Int.gcd r q = 1) {α : ℝ}
    (hα : |α - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (D : ℕ) (weights : ℕ → ℝ) (t H : ℝ) (hH : 1 ≤ H)
    (hw : ∀ d ∈ Finset.Icc 1 D, |weights d| ≤ 1) :
    ‖∑ n ∈ shortInterval t H, (divisorWeight D weights n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
      50 * (H / q + D + q) * Real.log (2 * (q : ℝ) * H) := by
  apply (divisorWeight_logLength_le hq hr hα D weights t H hH hw).trans
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hH0 : 0 ≤ H := by linarith
  have hscale := mul_le_mul_of_nonneg_left (typeI_log_scale hq hH)
    (show 0 ≤ 25 * (H / (q : ℝ) + D + q) by positivity)
  exact hscale.trans_eq (by ring)

/-- The exact rational phase version is the Type I bound used in Lemma 4.1. -/
theorem divisorWeight_exact_rational_le {q : ℕ} (hq : 0 < q) (r : ℤ)
    (hr : Int.gcd r q = 1) (D : ℕ) (weights : ℕ → ℝ) (t H : ℝ) (hH : 1 ≤ H)
    (hw : ∀ d ∈ Finset.Icc 1 D, |weights d| ≤ 1) :
    ‖∑ n ∈ shortInterval t H, (divisorWeight D weights n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((r : ℝ) * n / q)‖ ≤
      50 * (H / q + D + q) * Real.log (2 * (q : ℝ) * H) := by
  have hα : |(r : ℝ) / q - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    rw [sub_self, abs_zero]
    positivity
  have hb := divisorWeight_paper_log_le hq hr hα D weights t H hH hw
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  ring

#print axioms typeI_log_scale
#print axioms divisorWeight_paper_log_le
#print axioms divisorWeight_exact_rational_le
end LeanLab.Grimmelt2019.MainTerm
