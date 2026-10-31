/-
The ThetaWindow bridge applied to one published θ bound. P. Dusart, Estimates of some functions
over primes without R.H., arXiv 1002.0442v1, Theorem 5.2, page 4, table entry k = 2,
η₂ = 0.01, x₂ = 7713133853: |θ(x) - x| < 0.01 x / ln² x for x ≥ 7713133853. Read in Claude in
Chrome by run 20261018T2303Z-8776, from the PDF's content streams and then on the rendered page 4
in Chrome's PDF viewer: MATCH. The paper's bound is strict; the Prop uses ≤, which is weaker.
Cited as a Prop.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/
import LeanLab.Common.ThetaWindow

open Real

namespace LeanLab.Common.ThetaWindow

/-- Dusart 2010, Theorem 5.2, k = 2, η = 0.01, x ≥ 7713133853. Cited. -/
def DusartThm52k2 : Prop :=
  ∀ t : ℝ, 7713133853 ≤ t → |Chebyshev.theta t - t| ≤ 0.01 * t / Real.log t ^ 2

/-- CONDITIONAL ON `DusartThm52k2`: for every `x ≥ 7713133853` there is a prime in
`(x, x (1 + 1/(40 log² x))]`. -/
theorem prime_window_dusart (hD : DusartThm52k2) {x : ℝ} (hx : 7713133853 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (40 * Real.log x ^ 2)) := by
  have hx0 : 0 < x := by linarith
  have hL1 : 1 < Real.log x := by
    rw [← Real.log_exp 1]
    apply Real.log_lt_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  set L := Real.log x with hL
  have hL2 : 1 < L ^ 2 := by nlinarith
  set y := x * (1 + 1 / (40 * L ^ 2)) with hy
  have hxy : x ≤ y := by
    rw [hy]; have : 0 ≤ 1 / (40 * L ^ 2) := by positivity
    nlinarith
  have hLy : L ≤ Real.log y := Real.log_le_log hx0 hxy
  have hEy : 0.01 * y / Real.log y ^ 2 ≤ 0.01 * y / L ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by linarith) hLy 2
  apply prime_window_of_theta_bound (E := fun t => 0.01 * t / Real.log t ^ 2) (x0 := 7713133853)
    (by norm_num) hD hx hxy
  show 0.01 * x / Real.log x ^ 2 + 0.01 * y / Real.log y ^ 2 < y - x
  rw [← hL]
  have hL2pos : 0 < L ^ 2 := by positivity
  have key : 0.01 * x / L ^ 2 + 0.01 * y / L ^ 2 < y - x := by
    rw [hy]
    field_simp
    nlinarith
  linarith

end LeanLab.Common.ThetaWindow
