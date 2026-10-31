/-
P0013 Helfgott, Minor arcs for Goldbach's problem, arXiv 1205.5252v4, Section 5.1.1,
pages 51 and 52: the constants of (5.1) and (5.2), each against its printed defining bound.
Read by curl and pdftotext, every formula checked on the rendered page image,
cloud session 20261018T1650Z-cloud2.

All printed bounds hold except one: page 52 prints c₇,I = 6.19072 > 2√(3c₀c₁)/π, but
2√(3c₀c₁)/π = 6.1907227..., so the printed inequality fails by about 2.7e-6;
6.19073 works. `c7I_printed_fails` proves this. Cosmetic: c₇,I only multiplies a term of
the upper bound for |S_I,1|, and raising it by 1e-5 changes nothing downstream visibly.

AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.HelfgottArcs.MinorTypeI
open Real

/-- `c₀ = 31.521`, by Lemma A.5. -/
def c0 : ℝ := 31.521

/-- `c₁ = 1.0000028`. -/
def c1 : ℝ := 1.0000028

/-- `c₂ = 6π / (5√c₀)`. -/
noncomputable def c2 : ℝ := 6 * π / (5 * Real.sqrt c0)

theorem sqrt_c0_gt : (5.6143565 : ℝ) < Real.sqrt c0 := by
  rw [Real.lt_sqrt (by norm_num)]; unfold c0; norm_num

theorem sqrt_c0_lt : Real.sqrt c0 < 5.6143566 := by
  rw [Real.sqrt_lt' (by norm_num)]; unfold c0; norm_num

/-- `c₁ = 1.0000028 > 1 + (8 log 2)/V` for every `V ≥ 2·10⁶`. -/
theorem c1_ok (V : ℝ) (hV : 2 * 10 ^ 6 ≤ V) : 1 + 8 * Real.log 2 / V < c1 := by
  have hl := Real.log_two_lt_d9
  have hV0 : 0 < V := by linarith
  have : 8 * Real.log 2 / V ≤ 8 * Real.log 2 / (2 * 10 ^ 6) := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hV
  have : 8 * Real.log 2 / (2 * 10 ^ 6) < 0.0000028 := by
    rw [div_lt_iff₀ (by norm_num)]; linarith
  unfold c1; linarith

/-- `c₂ = 0.67147...`. -/
theorem c2_bounds : 0.67147 < c2 ∧ c2 < 0.67148 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have s1 := sqrt_c0_gt
  have s2 := sqrt_c0_lt
  have hs : 0 < 5 * Real.sqrt c0 := by linarith
  unfold c2
  constructor
  · rw [lt_div_iff₀ hs]; nlinarith
  · rw [div_lt_iff₀ hs]; nlinarith

/-- `c₀' = 0.798437 > c₀/(2π)²`. -/
theorem c0p_ok : c0 / (2 * π) ^ 2 < 0.798437 := by
  have p1 := Real.pi_gt_d20
  rw [div_lt_iff₀ (by positivity)]
  unfold c0; nlinarith

/-- `c₀'' = 1.685532`, rounding up `24 log 2 / π²`, the bound for `|(log·η)^(-δ)|`. -/
theorem c0pp_ok : 24 * Real.log 2 / π ^ 2 < 1.685532 := by
  have p1 := Real.pi_gt_d20
  have l := Real.log_two_lt_d9
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- `c₃,I = 2.11104 > c₀''/c₀'`. -/
theorem c3I_ok : (1.685532 : ℝ) / 0.798437 < 2.11104 := by norm_num

/-- `c₅,I = 3.57422 > 2√(c₀c₁)/π`. -/
theorem c5I_ok : 2 * Real.sqrt (c0 * c1) / π < 3.57422 := by
  have p1 := Real.pi_gt_d20
  have hs : Real.sqrt (c0 * c1) < 5.6143700 := by
    rw [Real.sqrt_lt' (by norm_num)]; unfold c0 c1; norm_num
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- `c₆,I = 2.23389 > 3c₁/(2c₂)`. -/
theorem c6I_ok : 3 * c1 / (2 * c2) < 2.23389 := by
  have p1 := Real.pi_gt_d20
  have s2 := sqrt_c0_lt
  have s1 := sqrt_c0_gt
  have hc2 : 0 < c2 := by unfold c2; positivity
  have e : 3 * c1 / (2 * c2) = 5 * c1 * Real.sqrt c0 / (4 * π) := by
    unfold c2
    have : Real.sqrt c0 ≠ 0 := by linarith
    field_simp
    ring
  rw [e, div_lt_iff₀ (by positivity)]
  unfold c1; nlinarith

/-- The value printed for `c₇,I`, 6.19072, is BELOW `2√(3c₀c₁)/π`, against page 52. -/
theorem c7I_printed_fails : (6.19072 : ℝ) < 2 * Real.sqrt (3 * c0 * c1) / π := by
  have p2 := Real.pi_lt_d20
  have p1 := Real.pi_gt_d6
  have hs : (9.724364 : ℝ) < Real.sqrt (3 * c0 * c1) := by
    rw [Real.lt_sqrt (by norm_num)]; unfold c0 c1; norm_num
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

theorem c7I_printed_not_ok : ¬ (2 * Real.sqrt (3 * c0 * c1) / π < 6.19072) :=
  not_lt.mpr c7I_printed_fails.le

/-- A corrected value: `6.19073 > 2√(3c₀c₁)/π`. -/
theorem c7I_corrected : 2 * Real.sqrt (3 * c0 * c1) / π < 6.19073 := by
  have p1 := Real.pi_gt_d20
  have hs : Real.sqrt (3 * c0 * c1) < 9.724365 := by
    rw [Real.sqrt_lt' (by norm_num)]; unfold c0 c1; norm_num
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- `c₈,I = 3.53017 > 2(8 log 2)/π`, with `|η₂'|₁ = 8 log 2`. -/
theorem c8I_ok : 2 * (8 * Real.log 2) / π < 3.53017 := by
  have p1 := Real.pi_gt_d20
  have l := Real.log_two_lt_d9
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- `c₉,I = 2.58877 > 3√2 c₁/(2√c₂)`. -/
theorem c9I_ok : 3 * Real.sqrt 2 * c1 / (2 * Real.sqrt c2) < 2.58877 := by
  have p1 := Real.pi_gt_d20
  have s1 := sqrt_c0_gt
  have s2 := sqrt_c0_lt
  have hc2 : 0 < c2 := by unfold c2; positivity
  have hsc2 : 0 < Real.sqrt c2 := Real.sqrt_pos.mpr hc2
  set X := 3 * Real.sqrt 2 * c1 / (2 * Real.sqrt c2) with hX
  have hX0 : 0 ≤ X := by rw [hX]; unfold c1; positivity
  have hsq : X ^ 2 = 15 * c1 ^ 2 * Real.sqrt c0 / (4 * π) := by
    rw [hX, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
      Real.sq_sqrt hc2.le]
    unfold c2
    have : Real.sqrt c0 ≠ 0 := by linarith
    field_simp
    ring
  have hlt : X ^ 2 < (2.58877 : ℝ) ^ 2 := by
    rw [hsq, div_lt_iff₀ (by positivity)]
    unfold c1; nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hlt

/-- `c₁₀,I = 9.37301 > c₀(1/2 - 2/π²)`. -/
theorem c10I_ok : c0 * (1 / 2 - 2 / π ^ 2) < 9.37301 := by
  have p2 := Real.pi_lt_d20
  have p1 := Real.pi_gt_d6
  have hp : 0 < π ^ 2 := by positivity
  have h : (c0 / 2 - 9.37301) * π ^ 2 < 2 * c0 := by unfold c0; nlinarith
  have e : c0 * (1 / 2 - 2 / π ^ 2) = c0 / 2 - 2 * c0 / π ^ 2 := by ring
  rw [e]
  have : (c0 / 2 - 9.37301) < 2 * c0 / π ^ 2 := by rw [lt_div_iff₀ hp]; exact h
  linarith

/-- `c₁₁,I = 9.0857 > c₀e³/(4π · 8 log 2)`. -/
theorem c11I_ok : c0 * Real.exp 3 / (4 * π * (8 * Real.log 2)) < 9.0857 := by
  have p1 := Real.pi_gt_d20
  have l := Real.log_two_gt_d9
  have e1 := Real.exp_one_lt_d9
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have hE : Real.exp 3 < 2.7182818286 ^ 3 := by
    rw [e3]; exact pow_lt_pow_left₀ e1 (Real.exp_pos 1).le (by norm_num)
  rw [div_lt_iff₀ (by positivity)]
  unfold c0; nlinarith

/-- Page 51 says "Clearly c₀''/c₀ > 1 > 2 - log 4"; with `c₀ = 31.521` the first
inequality is false. -/
theorem c0pp_div_c0_printed_fails : ¬ ((1.685532 : ℝ) / c0 > 1) := by
  unfold c0; norm_num

/-- What the folding into `c₃,I` needs, `c₀''/c₀' > 1 > 2 - log 4`, holds. -/
theorem c0pp_div_c0p_ok : (1.685532 : ℝ) / 0.798437 > 1 ∧ 1 > 2 - Real.log 4 := by
  refine ⟨by norm_num, ?_⟩
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  rw [h]; linarith

end LeanLab.HelfgottArcs.MinorTypeI
