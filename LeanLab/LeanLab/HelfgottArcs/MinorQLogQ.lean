/-
P0013 Helfgott, Minor arcs for Goldbach's problem, arXiv 1205.5252v4, pages 55 and 64 to 69.
Falsifier unit U-6724, CLOUD 20261020T1914Z-cloud49. Formulas read from the rendered page images.

The question S20 T2 T6 of the U-5013 harvest. At the parameters (5.44), UV = x/(2√(qδ₀)),
the c₁₄,I₂ term of (5.11) is c_ε c₁₄,I₂ (log q + log⁺ (6UV|δ|q/(√2 x))) x/(|δ|q), and
log q + log (3√2 √(|δ|q)) = (1/2) log (|δ| q³) + log (3√2); page 67 line 4 prints this,
correctly, as 3.30386 log δq³ + 16.4137. After (5.52) the same term is carried as
3.30386 log δq² + 16.4137, and page 69 bounds 4c₂ x/(qδ₀) (3.30386 log q² + 16.4137),
giving 8.874 log q and so q^{80/9} in (5.56) and in L_{x,δ,q} of (1.3). With q³ the
coefficient is 6 c₂ · 3.30386 > 13.31 > 80/9. Below: the gap, and the repaired bound
with q^{40/3}.

Also the question S14 to S17: page 67 says ε = 0.07, but 3.30386, 16.4137 and 29.7467 are
the ε = 0.05 values, while 2.49086 and 68.8137 are the ε = 0.07 values; and the constant
36.7795 omits the term c₁₆,I₂ · 6 · ((1+ε)/ε) · log 2, about 95.4 at ε = 0.07.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HelfgottArcs.MinorTypeI
import LeanLab.HelfgottArcs.MinorConstants

namespace LeanLab.HelfgottArcs.MinorQLogQ
open Real LeanLab.HelfgottArcs.MinorTypeI LeanLab.HelfgottArcs.MinorConstants

/-- `c_ε = (1 + ε)√(3 + 2ε)`, page 55. -/
noncomputable def ceps (ε : ℝ) : ℝ := (1 + ε) * Real.sqrt (3 + 2 * ε)

/-! ### The q exponent, S20 T2 T6 -/

/-- The term of (5.11) on page 67 has `log (|δ| q³) = log |δ| + 3 log q`. -/
theorem log_dq3 (d q : ℝ) (hd : 0 < d) (hq : 0 < q) :
    Real.log (d * q ^ 3) = Real.log d + 3 * Real.log q := by
  rw [Real.log_mul hd.ne' (by positivity), Real.log_pow]; push_cast; ring

/-- At the parameters (5.44), with `|δ| ≥ 8` and `δ₀ = |δ|/4`:
`log q + log (6UV|δ|q/(√2 x)) = (1/2) log (|δ| q³) + log (3√2)`, with `UV = x/(2√(qδ₀))`. -/
theorem log_argument_caseb (x d q : ℝ) (hx : 0 < x) (hd : 0 < d) (hq : 0 < q) :
    Real.log q + Real.log (6 * (x / (2 * Real.sqrt (q * (d / 4)))) * d * q / (Real.sqrt 2 * x))
      = (1 / 2) * Real.log (d * q ^ 3) + Real.log (3 * Real.sqrt 2) := by
  have hs : Real.sqrt (q * (d / 4)) = Real.sqrt (d * q) / 2 := by
    rw [show q * (d / 4) = (d * q) / 2 ^ 2 by ring, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num)]
  have hdq : 0 < d * q := mul_pos hd hq
  have hsq : 0 < Real.sqrt (d * q) := Real.sqrt_pos.mpr hdq
  have h2 : 0 < Real.sqrt 2 := by positivity
  have key : 6 * (x / (2 * Real.sqrt (q * (d / 4)))) * d * q / (Real.sqrt 2 * x)
      = 3 * Real.sqrt 2 * Real.sqrt (d * q) := by
    rw [hs]
    have e2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have edq : Real.sqrt (d * q) * Real.sqrt (d * q) = d * q := Real.mul_self_sqrt hdq.le
    field_simp
    nlinarith [e2, edq]
  rw [key, Real.log_mul (by positivity) hsq.ne', Real.log_sqrt hdq.le,
    Real.log_mul hd.ne' hq.ne', log_dq3 d q hd hq]
  ring

/-- The page 69 coefficient as printed, from `log q²`: `2 c₂ · 2 · 3.30386 ≤ 8.874 ≤ 80/9`. -/
theorem printed_coeff_q2 : 2 * c2 * (2 * 3.30386) ≤ 8.874 ∧ (8.874 : ℝ) ≤ 80 / 9 := by
  have ⟨_, h2⟩ := c2_bounds; constructor <;> nlinarith

/-- The coefficient from `log q³`: `13.31 < 2 c₂ · 3 · 3.30386`, above `80/9`. -/
theorem true_coeff_q3_gt : (13.31 : ℝ) < 2 * c2 * (3 * 3.30386) ∧
    (80 / 9 : ℝ) < 2 * c2 * (3 * 3.30386) := by
  have ⟨h1, _⟩ := c2_bounds; constructor <;> nlinarith

/-- The repaired coefficient: `2 c₂ · 3 · 3.30386 ≤ 40/3`. -/
theorem true_coeff_q3_le : 2 * c2 * (3 * 3.30386) ≤ 40 / 3 := by
  have ⟨_, h2⟩ := c2_bounds; nlinarith

/-- The bracket of page 69, the terms in `2x/(δ₀q)`, with the q³ of (5.11) kept:
`0.29315/2 + 2c₂ (3 · 3.30386 log q + 16.4137) + (3.30386/(e log 2)) log δ₀`. -/
noncomputable def bracketTrue (Lq Ld : ℝ) : ℝ :=
  0.29315 / 2 + 2 * c2 * (3 * 3.30386 * Lq + 16.4137) + 3.30386 / (Real.exp 1 * Real.log 2) * Ld

/-- The bound printed for it in (5.56) and (1.3): `log q^{80/9} δ₀^{16/9} + 111/5`. -/
noncomputable def bracketPrinted (Lq Ld : ℝ) : ℝ := 80 / 9 * Lq + 16 / 9 * Ld + 111 / 5

theorem e_log2_lt : Real.exp 1 * Real.log 2 < 1.8842 := by
  have e1 := Real.exp_one_lt_d9
  have l := Real.log_two_lt_d9
  have l0 := Real.log_two_gt_d9
  nlinarith

theorem T3_gt : (1.75 : ℝ) < 3.30386 / (Real.exp 1 * Real.log 2) := by
  have h := e_log2_lt
  have hp : 0 < Real.exp 1 * Real.log 2 := by positivity
  rw [lt_div_iff₀ hp]; nlinarith

/-- GAP, S20 T2 T6: for `log q ≥ 1` and `0 ≤ log δ₀ ≤ 100 log q`, the term the paper's own
(5.11) gives exceeds the bound printed in (5.56) and in `L_{x,δ,q}` of (1.3). -/
theorem gap (Lq Ld : ℝ) (hq : 1 ≤ Lq) (hd0 : 0 ≤ Ld) (hd1 : Ld ≤ 100 * Lq) :
    bracketPrinted Lq Ld < bracketTrue Lq Ld := by
  have ⟨h1, _⟩ := c2_bounds
  have t := T3_gt
  unfold bracketPrinted bracketTrue
  nlinarith [mul_le_mul_of_nonneg_right t.le hd0]

/-- REPAIR: the same term is at most `log q^{40/3} δ₀^{16/9} + 111/5`, for all
`log q, log δ₀ ≥ 0`. -/
theorem repair (Lq Ld : ℝ) (hq : 0 ≤ Lq) (hd0 : 0 ≤ Ld) :
    bracketTrue Lq Ld ≤ 40 / 3 * Lq + 16 / 9 * Ld + 111 / 5 := by
  have c := true_coeff_q3_le
  have t3 := T3_ok
  have t4 := T4_ok
  unfold bracketTrue
  have a : 2 * c2 * (3 * 3.30386 * Lq) ≤ 40 / 3 * Lq := by nlinarith
  have b : 3.30386 / (Real.exp 1 * Real.log 2) * Ld ≤ 16 / 9 * Ld :=
    mul_le_mul_of_nonneg_right (by linarith) hd0
  nlinarith

/-! ### The ε of page 67, S14 to S17 -/

theorem sqrt31_lt : Real.sqrt 3.1 < 1.7606817 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sqrt314_gt : (1.772 : ℝ) < Real.sqrt 3.14 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem sqrt2_gt : (1.41421 : ℝ) < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem log_3sqrt2_gt : (1.445 : ℝ) < Real.log (3 * Real.sqrt 2) := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by norm_num)]
  have := Real.log_three_gt_d9
  have := Real.log_two_gt_d9
  linarith

/-- With ε = 0.05: `c_ε c₁₄,I₂ / 2 ≤ 3.30386`, the printed coefficient. -/
theorem coeff_eps005 : ceps 0.05 * 3.57422 / 2 ≤ 3.30386 := by
  have s := sqrt31_lt
  have s0 : 0 ≤ Real.sqrt 3.1 := Real.sqrt_nonneg _
  have e3 : (3:ℝ) + 2 * 0.05 = 3.1 := by norm_num
  unfold ceps; rw [e3]; nlinarith

/-- With the ε = 0.07 that page 67 states: `c_ε c₁₄,I₂ / 2 > 3.388 > 3.30386`. -/
theorem coeff_eps007_gt : (3.388 : ℝ) < ceps 0.07 * 3.57422 / 2 := by
  have s := sqrt314_gt
  have e3 : (3:ℝ) + 2 * 0.07 = 3.14 := by norm_num
  unfold ceps; rw [e3]; nlinarith

/-- The first term 2.49086 is the ε = 0.07 value: `(c₄,I₂ + 1.07 c₁₃,I₂)/2 ≤ 2.49086`,
while at ε = 0.05 it is below 2.478. -/
theorem first_term_eps : (3.57422 + 1.07 * 1.31541) / 2 ≤ (2.49086 : ℝ) ∧
    (2.4908 : ℝ) < (3.57422 + 1.07 * 1.31541) / 2 ∧ (3.57422 + 1.05 * 1.31541) / 2 < (2.478 : ℝ) := by
  norm_num

/-- 68.8137 is `c₁₆,I₂ · 6 · ((1+ε)/ε)/2` at ε = 0.07, not at ε = 0.05. -/
theorem coeff_68_eps : (68.8136 : ℝ) < 1.50061 * 6 * ((1 + 0.07) / 0.07) / 2 ∧
    1.50061 * 6 * ((1 + 0.07) / 0.07) / 2 ≤ (68.8137 : ℝ) ∧
    (94 : ℝ) < 1.50061 * 6 * ((1 + 0.05) / 0.05) / 2 := by norm_num

/-- The term the constant 36.7795 omits: `c₁₆,I₂ · 6 · (1.07/0.07) · log 2 > 95`, while
36.7795 is exactly `12 c₁₆,I₂ + (3/4) c₁₇,I₂` rounded. -/
theorem missing_log2_term : (95 : ℝ) < 1.50061 * 6 * ((1 + 0.07) / 0.07) * Real.log 2 ∧
    (36.7794 : ℝ) < 12 * 1.50061 + 3 / 4 * 25.0295 ∧ 12 * 1.50061 + 3 / 4 * 25.0295 ≤ (36.7795 : ℝ) := by
  have := Real.log_two_gt_d9
  refine ⟨?_, by norm_num, by norm_num⟩
  nlinarith

/-- No single ε serves both 111/5 and the printed 16.4137 family: for every ε in [0.052, 1],
`0.29315/2 + 2 c₂ c_ε (c₁₄,I₂ log (3√2) + c₁₅,I₂) > 111/5`. With ε ≥ 0.0684 needed by
the x^{5/6} budget, see gen/minorQ_U6724.out, this is numerical evidence only for that half. -/
theorem const_fails_large_eps (ε : ℝ) (h0 : 0.052 ≤ ε) (_h1 : ε ≤ 1) :
    (111 / 5 : ℝ) < 0.29315 / 2 + 2 * c2 * (ceps ε * (3.57422 * Real.log (3 * Real.sqrt 2) + 3.71301)) := by
  have ⟨hc2, _⟩ := c2_bounds
  have hl := log_3sqrt2_gt
  have hs : (1.7618 : ℝ) < Real.sqrt (3 + 2 * ε) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith
  have hce : (1.052 : ℝ) * 1.7618 < ceps ε := by
    unfold ceps; nlinarith
  have hA : (3.57422 : ℝ) * 1.445 + 3.71301 < 3.57422 * Real.log (3 * Real.sqrt 2) + 3.71301 := by
    linarith
  have hprod : (1.052 : ℝ) * 1.7618 * (3.57422 * 1.445 + 3.71301) <
      ceps ε * (3.57422 * Real.log (3 * Real.sqrt 2) + 3.71301) := by
    have p1 : (0:ℝ) < 3.57422 * 1.445 + 3.71301 := by norm_num
    nlinarith
  nlinarith

/-! ### Page 66, S7: (5.9) carries c₁₀,I = 9.37301, page 66 evaluates with c₁₀,I₂ = 1.78783 -/

/-- The x^{2/3}/√(qδ₀) log x coefficient of page 66, by the page's own step
`1/(qδ₀) ≤ 1/(2√(qδ₀))`: with c₁₀,I₂ it is the printed 0.00828; with the c₁₀,I of (5.9)
and of the page 53 display it is above 0.0433. -/
theorem c10_slip : (1.78783 : ℝ) / 2 / 18 / 2 / 3 ≤ 0.00828 ∧
    (0.0433 : ℝ) < 9.37301 / 2 / 18 / 2 / 3 := by norm_num

end LeanLab.HelfgottArcs.MinorQLogQ
