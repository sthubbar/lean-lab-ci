import LeanLab.Common.ThetaWindowDusart

open Real

namespace LeanLab.Common.ThetaWindow

/-- LEAF: p. 4, display `x(1 + 1 / (40 \log^2 x))`. -/
theorem leaf1_dusart (x : ℝ) (hL1 : 1 < Real.log x) :
    let L := Real.log x; let y := x * (1 + 1 / (40 * L ^ 2)); x ≤ y := by
  intro L y
  have h1 : 0 < L ^ 2 := by positivity
  have h2 : 0 ≤ 1 / (40 * L ^ 2) := by positivity
  have hx0 : 0 < x := by
    sorry
  nlinarith

/-- LEAF: p. 4, L <= \log y. -/
theorem leaf2_dusart (x : ℝ) (hx0 : 0 < x) (hxy : x ≤ x * (1 + 1 / (40 * Real.log x ^ 2))) :
    Real.log x ≤ Real.log (x * (1 + 1 / (40 * Real.log x ^ 2))) := by
  exact Real.log_le_log hx0 hxy

/-- LEAF: p. 4, E(y) <= E(x). -/
theorem leaf3_dusart (x : ℝ) (hL1 : 1 < Real.log x) :
    let L := Real.log x; let y := x * (1 + 1 / (40 * L ^ 2));
    0.01 * y / Real.log y ^ 2 ≤ 0.01 * y / L ^ 2 := by
  intro L y
  have hx0 : 0 < x := by
    sorry
  have hxy : x ≤ y := by apply leaf1_dusart x hL1
  have hLy : L ≤ Real.log y := by apply leaf2_dusart x hx0 hxy
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by linarith) hLy 2

/-- LEAF: p. 4, E(x) + E(y) < y - x. -/
theorem leaf4_dusart (x : ℝ) (hL1 : 1 < Real.log x) :
    let L := Real.log x; let y := x * (1 + 1 / (40 * L ^ 2));
    0.01 * x / L ^ 2 + 0.01 * y / L ^ 2 < y - x := by
  intro L y
  have hL2pos : 0 < L ^ 2 := by positivity
  have hx0 : 0 < x := by
    sorry
  have hL2_gt : 1 < L ^ 2 := by nlinarith
  have hy : y = x * (1 + 1 / (40 * L ^ 2)) := rfl
  have key : 0.01 * x / L ^ 2 + 0.01 * y / L ^ 2 < y - x := by
    rw [hy]
    have key_inner : 0.01 * x / L ^ 2 + 0.01 * (x * (1 + 1 / (40 * L ^ 2))) / L ^ 2 < x * (1 + 1 / (40 * L ^ 2)) - x := by
      have h_lhs : 0.01 * x / L ^ 2 + 0.01 * (x * (1 + 1 / (40 * L ^ 2))) / L ^ 2 = x * (0.01 / L ^ 2 + 0.01 * (1 + 1 / (40 * L ^ 2)) / L ^ 2) := by ring
      have h_rhs : x * (1 + 1 / (40 * L ^ 2)) - x = x * (1 / (40 * L ^ 2)) := by ring
      rw [h_lhs, h_rhs]
      apply mul_lt_mul_of_pos_left _ hx0
      have h_sub_lhs : 0.01 / L ^ 2 + 0.01 * (1 + 1 / (40 * L ^ 2)) / L ^ 2 = (0.01 + 0.01 * (1 + 1 / (40 * L ^ 2))) / L ^ 2 := by ring
      rw [h_sub_lhs]
      have : (0.01 + 0.01 * (1 + 1 / (40 * L ^ 2))) / L ^ 2 = (0.02 + 0.01 / (40 * L ^ 2)) / L ^ 2 := by ring
      rw [this]
      have h_step : (0.02 + 0.01 / (40 * L ^ 2)) / L ^ 2 = 0.02 / L ^ 2 + 0.01 / (40 * L ^ 4) := by
        sorry
      rw [h_step]
      sorry
    exact key_inner
  exact key

/-- CONDITIONAL ON `DusartThm52k2`: for every `x ≥ 7713133853` there is a prime in
`(x, x (1 + 1/(40 log² x))]`. -/
theorem prime_window_dusart_decomp (hD : DusartThm52k2) {x : ℝ} (hx : 7713133853 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (40 * Real.log x ^ 2)) := by
  have hx0 : 0 < x := by linarith
  have hL1 : 1 < Real.log x := by
    rw [← Real.log_exp 1]
    apply Real.log_lt_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  set L := Real.log x with hL
  have hL2 : 1 < L ^ 2 := by nlinarith
  set y := x * (1 + 1 / (40 * L ^ 2)) with hy
  have hxy : x ≤ y := by apply leaf1_dusart x hL1
  have hLy : L ≤ Real.log y := by apply leaf2_dusart x hx0 hxy
  have hEy : 0.01 * y / Real.log y ^ 2 ≤ 0.01 * y / L ^ 2 := by apply leaf3_dusart x hL1
  apply prime_window_of_theta_bound (E := fun t => 0.01 * t / Real.log t ^ 2) (x0 := 7713133853)
    (by norm_num) hD hx hxy
  show 0.01 * x / Real.log x ^ 2 + 0.01 * y / Real.log y ^ 2 < y - x
  have key := leaf4_dusart x hL1
  rw [← hL]
  linarith

end LeanLab.Common.ThetaWindow
