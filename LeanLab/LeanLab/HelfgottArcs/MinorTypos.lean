/-
P0013 Helfgott, Minor arcs for Goldbach's problem, arXiv 1205.5252v4: four printed lines in
Section 5 that fail as printed, each with the arithmetic that shows it. Formulas read on the
rendered page images; cloud session 20261018T1650Z-cloud2.

1. Page 55: c₁₂,I₂ = 28.26771 > c₆,I₂ + c₁₀,I₂ log 2, with c₆,I₂ from page 54. The right side
   is about 29.322, so the printed constant is short by about 1.05.
2. Page 63: C₁ = 2.3536 is printed as about 510510/φ(510510) = 5.539; it is the square root.
3. Page 67: 16.404 ≤ 1.5785 x^{3/4 − 4/5} is false for every x ≥ 1; the exponent 4/5 − 3/4
   makes it true for x ≥ 2.16·10²⁰.
4. Page 71: max(y/2c₂, 2y) = y/2c₂ is false, the max is 2y; the bound the paper then uses,
   |δq| > y/2c₂, is still true.

AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HelfgottArcs.MinorTypeI

namespace LeanLab.HelfgottArcs.MinorTypos
open Real LeanLab.HelfgottArcs.MinorTypeI

/-- Page 54: `c₆,I₂ = 2√(3c₀c₁)/π + 3c₁/(2c₂) + 55c₀c₂/(6π²)`. -/
noncomputable def c6I2 : ℝ :=
  2 * Real.sqrt (3 * c0 * c1) / π + 3 * c1 / (2 * c2) + 55 * c0 * c2 / (6 * π ^ 2)

theorem c6I2_gt : 28.07 < c6I2 := by
  have a := c7I_printed_fails
  have ⟨h1, h2⟩ := c2_bounds
  have p := Real.pi_lt_d6
  have hc2 : 0 < c2 := by linarith
  have b : 2.2338 < 3 * c1 / (2 * c2) := by
    rw [lt_div_iff₀ (by positivity)]; unfold c1; nlinarith
  have c : 19.65 < 55 * c0 * c2 / (6 * π ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]; unfold c0; nlinarith [Real.pi_pos]
  unfold c6I2; linarith

/-- 1. The printed `c₁₂,I₂ = 28.26771` is below `c₆,I₂ + c₁₀,I₂ log 2`, in fact by more
than 1. -/
theorem c12I2_printed_fails : (28.26771 : ℝ) + 1 < c6I2 + 1.78783 * Real.log 2 := by
  have a := c6I2_gt
  have l := Real.log_two_gt_d9
  linarith

/-- 2. Page 63: `510510 = 2·3·5·7·11·13·17`, `φ = 1·2·4·6·10·12·16 = 92160`; the ratio is
about 5.539, its square root about 2.35359, which is the printed `C₁ = 2.3536`. -/
theorem C1_is_sqrt : (510510 : ℝ) / 92160 > 5.5 ∧
    Real.sqrt (510510 / 92160) < 2.3536 ∧ 2.3535 < Real.sqrt (510510 / 92160) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem primorial17 : (510510 : ℕ) = 2 * 3 * 5 * 7 * 11 * 13 * 17 ∧
    (92160 : ℕ) = 1 * 2 * 4 * 6 * 10 * 12 * 16 := by norm_num

/-- 3. As printed, `16.404 ≤ 1.5785 x^{3/4 − 4/5}` fails for every `x ≥ 1`. -/
theorem S25_printed_fails {x : ℝ} (hx : 1 ≤ x) :
    1.5785 * x ^ ((3 : ℝ) / 4 - 4 / 5) < 16.404 := by
  have : x ^ ((3 : ℝ) / 4 - 4 / 5) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  nlinarith

/-- 3. With the exponent `4/5 − 3/4 = 1/20` it holds for `x ≥ 2.16·10²⁰`. -/
theorem S25_corrected {x : ℝ} (hx : 2.16e20 ≤ x) :
    16.404 ≤ 1.5785 * x ^ ((4 : ℝ) / 5 - 3 / 4) := by
  have e : (4 : ℝ) / 5 - 3 / 4 = 1 / 20 := by norm_num
  rw [e]
  have h0 : (10.39215 : ℝ) ^ (20 : ℕ) ≤ 2.16e20 := by norm_num
  have h1 : (10.39215 : ℝ) ≤ x ^ ((1 : ℝ) / 20) := by
    have h2 : ((10.39215 : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) ≤ x ^ ((1 : ℝ) / 20) :=
      Real.rpow_le_rpow (by positivity) (h0.trans hx) (by norm_num)
    have h3 : ((10.39215 : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) = 10.39215 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rwa [h3] at h2
  nlinarith

/-- 4. Page 71: `1/(2c₂) < 2`, so `max(y/2c₂, 2y) = 2y` for `y > 0`, not `y/2c₂`. -/
theorem V11_max {y : ℝ} (hy : 0 < y) : max (y / (2 * c2)) (2 * y) = 2 * y ∧
    y / (2 * c2) < 2 * y := by
  have ⟨h1, _⟩ := c2_bounds
  have hlt : y / (2 * c2) < 2 * y := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  exact ⟨max_eq_right hlt.le, hlt⟩

end LeanLab.HelfgottArcs.MinorTypos
