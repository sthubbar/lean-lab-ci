/-
P0014 H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Prop. 4.11 for
`η = η₊`, p. 52, Lemma 4.4's coefficients `1.631, 12.42, 1.321, 34.51`, from Appendix B,
(B.17) to (B.30), pages 73 and 74. Unit U-6066, CLOUD 20261020T0516Z-cloud35. All MATCH.

Cited, checked in Python only (numerics/sec45_check.py): `|η♦ · log|₂ ≤ 0.3220301` of (B.27), value
0.32203007, and `|h(t)/√t|₂ ≤ 1.5023459` of (B.29), value 1.50234581, a difference of two numbers
near 1470 that needs `e` to more digits than Mathlib's `exp_one_lt_d9`; and (B.23)'s `274.8569`,
(B.26)'s `|η◦|₂ = 0.8001287…`.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.HelfgottMajor.Sec48

namespace LeanLab.HelfgottMajor.Prop411Lemma44
open Real LeanLab.HelfgottMajor.Sec45

lemma H_pow {H : ℝ} (hH : 50 ≤ H) : 883882 ≤ H ^ (7 / 2 : ℝ) := by
  have h0 : 0 ≤ H := by linarith
  have e : H ^ (7 / 2 : ℝ) = H ^ 3 * √H := by
    rw [show (7 / 2 : ℝ) = (3 : ℕ) + 1 / 2 by norm_num, Real.rpow_add (by linarith),
      Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [e]
  have hs : 7.07106 ≤ √H := by rw [Real.le_sqrt (by norm_num) h0]; nlinarith
  have h3 : (50 : ℝ) ^ 3 ≤ H ^ 3 := pow_le_pow_left₀ (by norm_num) hH 3
  norm_num at h3
  nlinarith [mul_le_mul h3 hs (by norm_num) (by positivity)]

/-- **(B.25) with `H ≥ 50`: `|η₊|₂ ≤ 0.800129 + 274.8569/H^{7/2} ≤ 0.80044`**, MATCH, 0.80043997; and
the lower bound `|η◦|₂ − 274.8569/H^{7/2} ≥ 0.799817`. -/
theorem etaP_bounds {H : ℝ} (hH : 50 ≤ H) :
    0.800129 + 274.8569 / H ^ (7 / 2 : ℝ) ≤ 0.80044 ∧
      0.799817 ≤ 0.8001287 - 274.8569 / H ^ (7 / 2 : ℝ) := by
  have h := H_pow hH
  have hp : 0 < H ^ (7 / 2 : ℝ) := by linarith
  have : 274.8569 / H ^ (7 / 2 : ℝ) ≤ 274.8569 / 883882 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h
  constructor <;> norm_num at this ⊢ <;> linarith

/-- **(B.28): `|M h(ir)|₁/(2π) · 0.3220301 ≤ 0.8299818`** with (B.17)'s `16.193918`, MATCH,
values 2.5773421 and 0.82998173. -/
theorem etaP_log : 16.193918 / (2 * π) ≤ (2.5773421 : ℝ) ∧ (2.5773421 : ℝ) * 0.3220301 ≤ 0.8299818 := by
  have := pi_gt_d20
  refine ⟨?_, by norm_num⟩
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- **(B.30): `1.5023459/√2 ≤ 1.062319`**, MATCH, 1.06231897. -/
theorem b30_const : 1.5023459 / √2 ≤ (1.062319 : ℝ) := by
  have h : (1.41421356 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- **Prop. 4.11, Lemma 4.4's coefficient of `√T₀ log qT₀`: `|η₊|₂ + |η₊ · log|₂ ≤ 1.631`**, MATCH,
1.6304218. -/
theorem coef1 {a b : ℝ} (ha : a ≤ 0.80044) (hb : b ≤ 0.8299818) : a + b ≤ 1.631 := by linarith

/-- **the coefficient of `√T₀`: `17.21 |η₊ · log|₂ − log(2π√e) |η₊|₂ ≤ 12.42`** for
`|η₊ · log|₂ ≤ 0.8299818`, `|η₊|₂ ≥ 0.799817`, MATCH, 12.41411. -/
theorem coef2 {a b : ℝ} (ha : 0.799817 ≤ a) (hb : b ≤ 0.8299818) :
    17.21 * b - log (2 * π * √(exp 1)) * a ≤ 12.42 := by
  have h := LeanLab.HelfgottMajor.Sec48.log_two_pi_sqrt_e.1
  nlinarith

/-- **the `log q` and constant terms: `|η₊/√t|₁ ≤ 1.062319 √Γ(3/2)` by (B.30) at `σ = −1/2`, and
`1.32 · 1.062319 √(√π/2) ≤ 1.321`, `34.5 · 1.062319 √(√π/2) ≤ 34.51`**, MATCH, 1.320083 and 34.50218. -/
theorem coef34 : 1.32 * (1.062319 * √nTwo) ≤ (1.321 : ℝ) ∧ 34.5 * (1.062319 * √nTwo) ≤ (34.51 : ℝ) := by
  have h := sqrt_nTwo_lt
  constructor <;> nlinarith

end LeanLab.HelfgottMajor.Prop411Lemma44
