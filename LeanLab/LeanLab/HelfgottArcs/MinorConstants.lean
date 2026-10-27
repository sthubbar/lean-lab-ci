/-
P0013 Helfgott, Minor arcs for Goldbach's problem, arXiv 1205.5252v4, Section 5, pages 55
to 73: printed constants that are single explicit inequalities, each against its printed
definition. Read by curl and pdftotext, formulas checked on the rendered page images by a
harvest subagent and re-read here; cloud session 20261018T1650Z-cloud2.
All of these MATCH. AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HelfgottArcs.MinorTypeI

namespace LeanLab.HelfgottArcs.MinorConstants
open Real LeanLab.HelfgottArcs.MinorTypeI

theorem sqrt_c0c1_gt : (5.6143644 : ℝ) < Real.sqrt (c0 * c1) := by
  rw [Real.lt_sqrt (by norm_num)]; unfold c0 c1; norm_num

theorem sqrt_c0c1_lt : Real.sqrt (c0 * c1) < 5.6143645 := by
  rw [Real.sqrt_lt' (by norm_num)]; unfold c0 c1; norm_num

/-! ### Page 55, the constants of Section 5.1.2 -/

theorem c2_lt_tight : c2 < 0.6714771 := by
  have p := Real.pi_lt_d20
  have s := sqrt_c0_gt
  unfold c2
  rw [div_lt_iff₀ (by linarith)]; nlinarith

/-- `c₉,I₂ = 0.82214 > 3c₁ · 1.0004 / (2e c₂)`. -/
theorem c9I2_ok : 3 * c1 * 1.0004 / (2 * Real.exp 1 * c2) < 0.82214 := by
  have e1 := Real.exp_one_gt_d9
  have ⟨h1, _⟩ := c2_bounds
  rw [div_lt_iff₀ (by positivity)]
  unfold c1; nlinarith

/-- `c₁₀,I₂ = 1.78783 > 1.0004 √(c₀c₁)/π`. -/
theorem c10I2_ok : 1.0004 * Real.sqrt (c0 * c1) / π < 1.78783 := by
  have p := Real.pi_gt_d20
  have s := sqrt_c0c1_lt
  rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- `c₁₃,I₂ = 1.31541 > 2√(c₀c₁) · 1.0004/(πe)`. -/
theorem c13I2_ok : 2 * Real.sqrt (c0 * c1) * 1.0004 / (π * Real.exp 1) < 1.31541 := by
  have p := Real.pi_gt_d20
  have e1 := Real.exp_one_gt_d9
  have s := sqrt_c0c1_lt
  rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- `c₁₅,I₂ = 3.71301 > 2√(c₀c₁) · 1.03883/π`. -/
theorem c15I2_ok : 2 * Real.sqrt (c0 * c1) * 1.03883 / π < 3.71301 := by
  have p := Real.pi_gt_d20
  have s := sqrt_c0c1_lt
  rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- `c₁₆,I₂ = 1.50061 > 1.0004 · 3c₁/2`. -/
theorem c16I2_ok : 1.0004 * (3 * c1 / 2) < 1.50061 := by unfold c1; norm_num

/-- `c₁₇,I₂ = 25.0295 > 1.0004 · 35c₀c₂/(3π²)`. -/
theorem c17I2_ok : 1.0004 * (35 * c0 * c2) / (3 * π ^ 2) < 25.0295 := by
  have p := Real.pi_gt_d20
  have h2 := c2_lt_tight
  rw [div_lt_iff₀ (by positivity)]
  unfold c0; nlinarith

/-- `c₁₈,I₂ = 3.57565 > 2.0008 √(c₀c₁)/π`. -/
theorem c18I2_ok : 2.0008 * Real.sqrt (c0 * c1) / π < 3.57565 := by
  have p := Real.pi_gt_d20
  have s := sqrt_c0c1_lt
  rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- `c₈,I₂ = 1.17257 > (c₁₀,I/4) · 0.5004` and `c₅,I₂ = 3.53312 > 1.0004 c₈,I`. -/
theorem c8I2_c5I2_ok : (9.37301 : ℝ) / 4 * 0.5004 < 1.17257 ∧ (1.0004 : ℝ) * 3.53017 < 3.53312 := by
  constructor <;> norm_num

/-! ### Pages 56 and 57, `κ₁`, `κ₉`, `κ₂` -/

theorem sqrt_5e5_gt : (707.1067811 : ℝ) < Real.sqrt 500000 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

/-- `κ₁ = 2/π² + 22.6418/√(10⁶/2)`, (5.15). -/
noncomputable def κ1 : ℝ := 2 / π ^ 2 + 22.6418 / Real.sqrt 500000

theorem κ1_lt : κ1 < 0.23466271 := by
  have p := Real.pi_gt_d20
  have s := sqrt_5e5_gt
  have a : 2 / π ^ 2 < 0.2026423673 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have b : 22.6418 / Real.sqrt 500000 < 0.0320203407 := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  unfold κ1; linarith

theorem κ1_pos : 0 < κ1 := by unfold κ1; positivity

/-- (5.15): `κ₁ ≤ 0.2347`. -/
theorem κ1_le : κ1 ≤ 0.2347 := by linarith [κ1_lt]

/-- Page 56: `κ₉ = 8√(1.0172 κ₁) ≤ 3.9086`, with κ₁ unrounded. -/
theorem κ9_le : 8 * Real.sqrt (1.0172 * κ1) ≤ 3.9086 := by
  have h := κ1_lt
  have : Real.sqrt (1.0172 * κ1) ≤ 3.9086 / 8 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [κ1_pos]
  linarith

/-- Page 57: `κ₂ = 4√κ₁ ≤ 1.93768`, margin about 1.2e-7. -/
theorem κ2_le : 4 * Real.sqrt κ1 ≤ 1.93768 := by
  have h := κ1_lt
  have : Real.sqrt κ1 ≤ 1.93768 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [κ1_pos]
  linarith

/-! ### Pages 65 to 73 -/

/-- Page 65: `x₀^{1/6} = 1000√6` for `x₀ = 2.16·10²⁰`, so `2√6/x₀^{1/6} = 0.002`. -/
theorem x0_sixth : (1000 * Real.sqrt 6) ^ 6 = (2.16e20 : ℝ) ∧
    2 * Real.sqrt 6 / (1000 * Real.sqrt 6) = 0.002 := by
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · have : (1000 * Real.sqrt 6) ^ 6 = 1000 ^ 6 * (Real.sqrt 6 ^ 2) ^ 3 := by ring
    rw [this, h6]; norm_num
  · field_simp; norm_num

/-- Page 66: `log(27/2) + 2/5 + c₃,I + c₄,I ≤ 6.11676`, margin about 3e-7. -/
theorem S1_ok : Real.log (27 / 2) + 2 / 5 + 2.11104 + 1.00303 ≤ 6.11676 := by
  have e : Real.log (27 / 2) = 3 * Real.log 3 - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (27 : ℝ) = 3 ^ 3 by norm_num,
      Real.log_pow]; push_cast; ring
  have := Real.log_three_lt_d9
  have := Real.log_two_gt_d9
  rw [e]; linarith

/-- Page 66, (5.51): `log 108 + 4/5 ≤ 5.48214`. -/
theorem S9_ok : Real.log 108 + 4 / 5 ≤ 5.48214 := by
  have e : Real.log 108 = 2 * Real.log 2 + 3 * Real.log 3 := by
    rw [show (108 : ℝ) = 2 ^ 2 * 3 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]; push_cast; ring
  have := Real.log_three_lt_d9
  have := Real.log_two_lt_d9
  rw [e]; linarith

/-- Page 69: `3.30386/(e log 2) ≤ 1.7535 ≤ 16/9`. -/
theorem T3_ok : 3.30386 / (Real.exp 1 * Real.log 2) ≤ 1.7535 := by
  have e1 := Real.exp_one_gt_d9
  have l := Real.log_two_gt_d9
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- Page 69: `0.29315/2 + 2c₂ · 16.4137 ≤ 22.19 ≤ 111/5`. -/
theorem T4_ok : 0.29315 / 2 + 2 * c2 * 16.4137 ≤ 22.19 := by
  have ⟨_, h2⟩ := c2_bounds; linarith

/-- Pages 69 to 73, sums of printed numbers. -/
theorem printed_sums :
    (6.11676 : ℝ) + 2.74107 ≤ 8.858 ∧ (8.858 : ℝ) ≤ 80 / 9 ∧ (5.515 : ℝ) ≤ 50 / 9 ∧
    (22.19 : ℝ) ≤ 111 / 5 ∧ (8.874 : ℝ) ≤ 80 / 9 ∧ (1.7535 : ℝ) ≤ 16 / 9 ∧
    (4.1982 : ℝ) + 1213.15 ≤ 1217.35 ∧ (0.27125 : ℝ) * 0.08659 * 0.002 ≤ 0.000047 ∧
    (0.4141 : ℝ) + 0.000047 ≤ 0.41415 ∧ (3.14624 : ℝ) ≤ 3.2 := by
  norm_num

end LeanLab.HelfgottArcs.MinorConstants
