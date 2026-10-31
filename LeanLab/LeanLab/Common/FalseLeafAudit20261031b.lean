/-
Second part of the 2026-10-31 false leaf audit, run 20261031T2235Z-16111, architect: the same
bug class, a real variable under `Real.log` with no positivity or range hypothesis, found by a
sweep of all 231 Decomp files on main at e8b544e8. Each `*_old` Prop is the leaf as it stood on
main, word for word. AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Akeno2026.Statements
import Mathlib

namespace LeanLab.Common.FalseLeafAudit20261031b

open Real Chebyshev

/-- RieselVaughan1983/DecompJ206 `theta_bound_4_3` as on main at e8b544e8. -/
def theta_bound_4_3_old : Prop := ∀ x : ℝ, 3000 ≤ Real.log x →
    |θ x - x| < 154 / 1000000 * x / Real.log x

/-- RieselVaughan1983/DecompJ206 `theta_bound_4_4` as on main at e8b544e8. -/
def theta_bound_4_4_old : Prop := ∀ x : ℝ, 22 ≤ Real.log x → Real.log x ≤ 5000 →
    |θ x - x| < 822 / 100000 * x / Real.log x

/-- At negative x with log x = L > 0, θ x = 0, so |θ x - x| = -x > 0 while c x / L < 0. -/
theorem neg_exp_fails (L c : ℝ) (hL : 0 < L) (hc : 0 < c) :
    ¬ (|θ (-Real.exp L) - (-Real.exp L)| < c * (-Real.exp L) / Real.log (-Real.exp L)) := by
  rw [Real.log_neg_eq_log, Real.log_exp, theta_eq_zero_of_le_one (by
    have := Real.exp_pos L; linarith)]
  intro h
  have he := Real.exp_pos L
  have h1 : c * -Real.exp L / L < 0 := div_neg_of_neg_of_pos (by nlinarith) hL
  have h2 : 0 ≤ |(0:ℝ) - -Real.exp L| := abs_nonneg _
  linarith

theorem theta_bound_4_3_old_false : ¬ theta_bound_4_3_old := by
  intro h
  have := h (-Real.exp 3000) (by rw [Real.log_neg_eq_log, Real.log_exp])
  exact neg_exp_fails 3000 (154 / 1000000) (by norm_num) (by norm_num) this

theorem theta_bound_4_4_old_false : ¬ theta_bound_4_4_old := by
  intro h
  have := h (-Real.exp 22) (by rw [Real.log_neg_eq_log, Real.log_exp])
    (by rw [Real.log_neg_eq_log, Real.log_exp]; norm_num)
  exact neg_exp_fails 22 (822 / 100000) (by norm_num) (by norm_num) this

/-- Vacuity of the repaired RieselVaughan leaves: x = exp 3000 meets 0 < x, 3000 ≤ log x, and
x = exp 22 meets 0 < x, 22 ≤ log x ≤ 5000. -/
theorem riesel_vaughan_hyps_hold :
    0 < Real.exp 3000 ∧ 3000 ≤ Real.log (Real.exp 3000) ∧
    0 < Real.exp 22 ∧ 22 ≤ Real.log (Real.exp 22) ∧ Real.log (Real.exp 22) ≤ 5000 := by
  simp only [Real.log_exp]; exact ⟨Real.exp_pos _, le_rfl, Real.exp_pos _, le_rfl, by norm_num⟩

open LeanLab.Akeno2026

/-- Akeno2026/DecompJ267 `thm1_1_triangle_bound` as on main at e8b544e8, no hypotheses. -/
def thm1_1_triangle_bound_old : Prop := ∀ (θ' : ℝ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N d : ℕ) (l : ℤ),
    ‖Rdl w₁ w₂ X N d l‖ ≤ X / d * Real.log X ^ 2

/-- At X = 1 the right side is 0, so the leaf forces R_{1,0}(4) = 0 for all weights. Weights
1{2} ⊗ 1{2} give log² 2 - K and 1{1} ⊗ 1{3} give -K, K = singSeries 4 / psiN 4 1; both zero is
impossible. -/
theorem thm1_1_triangle_bound_old_false : ¬ thm1_1_triangle_bound_old := by
  intro h
  have hz : ∀ w₁ w₂ : ℝ → ℝ, Rdl w₁ w₂ 1 4 1 0 = 0 := by
    intro w₁ w₂
    have := h 0 w₁ w₂ 1 4 1 0
    simp only [Real.log_one] at this
    norm_num at this
    exact this
  have e1 := hz (fun t => if t = 2 then 1 else 0) (fun t => if t = 2 then 1 else 0)
  have e2 := hz (fun t => if t = 1 then 1 else 0) (fun t => if t = 3 then 1 else 0)
  simp only [Rdl, Finset.sum_range_succ, Finset.sum_range_zero, Int.modEq_one, if_true,
    div_one] at e1 e2
  norm_num at e1 e2
  have hl2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [hl2] at e1
  have hK : singSeries 4 / psiN 4 1 = 0 := by rcases e2 with h0 | h0 <;> simp [h0]
  rw [hK, sub_zero] at e1
  nlinarith [e1, hpos]

/-- Akeno2026/DecompJ267 `thm1_1_cauchy_schwarz` as on main at e8b544e8. The exponent `1/2` is
a natural number literal there, so `1/2 = 0` and both powers are 1: the leaf says only
`levelSum θ k w₁ w₂ X N ≤ 1`, which is not the paper's Cauchy-Schwarz step. -/
theorem thm1_1_cauchy_schwarz_old_is_le_one (θ' : ℝ) (k : ℕ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N : ℕ) :
    (levelSum θ' k w₁ w₂ X N ≤
      (X * Real.log X ^ 2) ^ (1/2) * (levelSum θ' 0 w₁ w₂ X N) ^ (1/2)) ↔
    levelSum θ' k w₁ w₂ X N ≤ 1 := by
  norm_num

end LeanLab.Common.FalseLeafAudit20261031b
