import LeanLab.ChirreHagen2025.Decomp429a
import LeanLab.ChirreHagen2025.Decomp429b
import LeanLab.ChirreHagen2025.Decomp429c

/-!
P0075 pages 4 and 5, Lemmas 2.2 and 2.3.
These bridges use the task429 components and retain every cited input.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp429d
open MeasureTheory Decomp377a Decomp377d

/-- P0075 page 4 and Chandee Lemma 2.3, with the large region decomposed.
CONDITIONAL ON the Binet identity, small region and three task429 integral leaves. -/
theorem gamma_log_derivative (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re) :
    (deriv Complex.Gamma z / Complex.Gamma z).re ≤ Real.log ‖z‖ := by
  rw [(binet_identity z hz).2]
  by_cases hn : 4 ≤ ‖z‖
  · linarith [Decomp429a.large_correction z hz hn]
  · linarith [small_correction z hz (lt_of_not_ge hn)]

/-- Exact inherited composed-Gamma target from P0075 page 4.
CONDITIONAL ON the same explicit gamma inputs. -/
theorem leaf_gamma_bound (s : ℂ) (h_re : s.re ≥ 0) (h_im : s.im ≠ 0) :
    (deriv (fun z => Complex.Gamma (z / 2 + 1)) s / Complex.Gamma (s / 2 + 1)).re ≤
    Real.log |s.im| - Real.log 2 + (s.re + 2) ^ 2 / (2 * s.im ^ 2) := by
  have hr : 1 ≤ (s / 2 + 1).re := by simp [Complex.div_re]; linarith
  have hn : 1 ≤ ‖s / 2 + 1‖ := hr.trans (Complex.re_le_norm _)
  have hl : 0 ≤ Real.log ‖s / 2 + 1‖ := Real.log_nonneg hn
  have hg := gamma_log_derivative (s / 2 + 1) (by linarith)
  rw [gamma_chain s h_re]
  apply le_trans (show (1 / 2 : ℝ) *
    (deriv Complex.Gamma (s / 2 + 1) / Complex.Gamma (s / 2 + 1)).re ≤
      Real.log ‖s / 2 + 1‖ by linarith)
  exact shifted_log_norm s h_re h_im

/-- Exact inherited DecompJ932 mean-square target from P0075 pages 4 and 5.
CONDITIONAL ON the pointwise Selberg leaf, the finite mean-value leaf and
inherited cited Appendix inputs. No old mean-square sorry is used. -/
theorem leaf_integration_step : RiemannHypothesis → ∀ T : ℝ, 4 * 10 ^ 13 ≤ T →
  (∫ t in (10 ^ 4 : ℝ)..T,
    ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I)‖ ^ 2)
    ≤ 0.8056 * T := by
  intro hRH T hT
  have he := Decomp429b.remainder_mean_square hRH T hT
  apply (weighted_split T (by linarith) he.1).trans
  apply le_trans (add_le_add
    (mul_le_mul_of_nonneg_left (Decomp429c.polynomial_mean_square hRH T hT) (by norm_num))
    (mul_le_mul_of_nonneg_left he.2 (by norm_num)))
  exact final_arithmetic T hT

/-- P0075 Lemma 2.3 from the refined smaller inputs.
CONDITIONAL ON the same analytic and Appendix inputs. -/
theorem lemma2_3_assembled : Additional122.lemma2_3 := by
  exact leaf_integration_step

end LeanLab.ChirreHagen2025.Decomp429d
