/-
P0013 Helfgott, Minor arcs for Goldbach's problem, arXiv 1205.5252v4, page 73, the proof
of the Main Theorem. Falsifier unit U-6724, CLOUD 20261020T1914Z-cloud49; formulas read
from the rendered page image at 250 dpi.

Page 73 applies √(AB) ≤ (A/√ρ + √ρ B)/2 with A = C_{x,δ₀q}(log δ₀q + 0.002) + log(4δ₀q)/2
and B = 0.30214 log δ₀q + 0.67506. The constant term of the right side is
(1/2)(log 2/√ρ + √ρ · 0.67506), but the page prints (1/2)(log 2/√ρ + (√ρ/2) · 0.67506)
and evaluates it as 0.49911; at the page's ρ = 3.39796 the true value is 0.81020. The
Main Theorem's main term R log δ₀q + 0.5 in (1.2) rests on this 0.49911.

Below: no ρ > 0 makes the constant term 0.5 or less, `amgm_const_gt`; and the printed
final inequality of page 73, line 4, fails at x = x₀ = 2.16·10²⁰, t = δ₀q = 2,
`printed_line4_fails`. This is a gap in the proof of the stated constant 0.5, not a
proof that the Main Theorem is false. Also C_{x₀,2}/log 2 > 0.08659, `C_ratio_at_2`,
against the page's "C_{x,t}/log t ≤ 0.08659 for t ≤ 10⁶".

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.HelfgottArcs.MinorQAMGM
open Real

/-- `C_{x,t} = log (1 + log 4t / (2 log (9x^{1/3}/(2.004 t))))`, (5.57). -/
noncomputable def Cxt (x t : ℝ) : ℝ :=
  Real.log (1 + Real.log (4 * t) / (2 * Real.log (9 * x ^ ((1 : ℝ) / 3) / (2.004 * t))))

/-- The left side of the page 73 display, at `C = C_{x,t}` and `L = log t`. -/
noncomputable def lhs (C L : ℝ) : ℝ :=
  Real.sqrt (C * (L + 0.002) + (Real.log 4 + L) / 2) * Real.sqrt (0.30214 * L + 0.67506)

/-- The printed right side of page 73, line 4. -/
def printedRhs (C L : ℝ) : ℝ := 0.27125 * C * (L + 0.002) + 0.4141 * L + 0.49911

/-- For every `s = √ρ > 0`, the true AM-GM constant term exceeds 0.68 > 0.5. -/
theorem amgm_const_gt (s : ℝ) (hs : 0 < s) :
    (0.68 : ℝ) < (Real.log 2 / s + s * 0.67506) / 2 := by
  have l := Real.log_two_gt_d9
  have key : 1.36 * s < Real.log 2 + s * s * 0.67506 := by nlinarith [sq_nonneg (s - 1.0073)]
  have h : 1.36 < Real.log 2 / s + s * 0.67506 := by
    rw [div_add' _ _ _ hs.ne', lt_div_iff₀ hs]; nlinarith
  linarith

/-- The printed form of that constant gives 0.49911 at ρ = 3.39796; the true form gives
more than 0.81. Here `s` is any number with `1.8433 ≤ s ≤ 1.8434`, and √3.39796 is one. -/
theorem printed_vs_true_const (s : ℝ) (h1 : 1.8433 ≤ s) (h2 : s ≤ 1.8434) :
    (Real.log 2 / s + s / 2 * 0.67506) / 2 < 0.4992 ∧
    (0.81 : ℝ) < (Real.log 2 / s + s * 0.67506) / 2 := by
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have hs : 0 < s := by linarith
  have a : Real.log 2 / s < 0.37605 := by rw [div_lt_iff₀ hs]; nlinarith
  have b : 0.37600 < Real.log 2 / s := by rw [lt_div_iff₀ hs]; nlinarith
  constructor <;> nlinarith

theorem sqrt_3_39796 : 1.8433 ≤ Real.sqrt 3.39796 ∧ Real.sqrt 3.39796 ≤ 1.8434 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- `x₀^{1/3} = 6·10⁶`. -/
theorem x0_cbrt : (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) = 6e6 := by
  have h : (2.16e20 : ℝ) = (6e6 : ℝ) ^ (3 : ℕ) := by norm_num
  rw [h, show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

theorem exp16_lt : Real.exp 16 < 8886111 := by
  have e := Real.exp_one_lt_d9
  have h : Real.exp 16 = Real.exp 1 ^ 16 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 16 < (2.7182818286 : ℝ) ^ 16 :=
        pow_lt_pow_left₀ e (Real.exp_pos 1).le (by norm_num)
    _ < 8886111 := by norm_num

theorem exp16_gt : 8886110 < Real.exp 16 := by
  have e := Real.exp_one_gt_d9
  have h : Real.exp 16 = Real.exp 1 ^ 16 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc (8886110 : ℝ) < (2.7182818283 : ℝ) ^ 16 := by norm_num
    _ < Real.exp 1 ^ 16 := pow_lt_pow_left₀ e (by norm_num) (by norm_num)

/-- `exp x ≤ 1/(1 - x)` for `x < 1`. -/
theorem exp_le_inv_one_sub (x : ℝ) (hx : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have h := Real.add_one_le_exp (-x)
  have hp : 0 < Real.exp (-x) := Real.exp_pos _
  have e : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The denominator at x₀, t = 2: `16.3 < log (9 · 6·10⁶/(2.004 · 2)) < 16.5`. -/
theorem den_bounds : 16.3 < Real.log (9 * (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / (2.004 * 2)) ∧
    Real.log (9 * (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / (2.004 * 2)) < 16.5 := by
  rw [x0_cbrt]
  constructor
  · rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have : Real.exp 16.3 = Real.exp 16 * Real.exp 0.3 := by rw [← Real.exp_add]; norm_num
    have h3 := exp_le_inv_one_sub 0.3 (by norm_num)
    rw [this]
    have h3' : Real.exp 0.3 ≤ 1.4286 := by
      calc Real.exp 0.3 ≤ 1 / (1 - 0.3) := h3
        _ ≤ 1.4286 := by norm_num
    nlinarith [exp16_lt, Real.exp_pos 0.3, Real.exp_pos 16]
  · rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have : Real.exp 16.5 = Real.exp 16 * (Real.exp 0.25 * Real.exp 0.25) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    have h25 : 1.25 ≤ Real.exp 0.25 := by linarith [Real.add_one_le_exp (0.25 : ℝ)]
    rw [this]; nlinarith [exp16_gt]

theorem log8 : Real.log (4 * 2) = 3 * Real.log 2 := by
  rw [show (4 : ℝ) * 2 = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring

/-- `0 ≤ C_{x₀,2} ≤ 0.12`. -/
theorem C_x0_2 : 0 ≤ Cxt 2.16e20 2 ∧ Cxt 2.16e20 2 ≤ 0.12 := by
  have ⟨d1, _⟩ := den_bounds
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  unfold Cxt
  rw [log8]
  set D := Real.log (9 * (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / (2.004 * 2))
  have hD : 0 < 2 * D := by linarith
  have u0 : 0 ≤ 3 * Real.log 2 / (2 * D) := div_nonneg (by linarith) hD.le
  have u1 : 3 * Real.log 2 / (2 * D) ≤ 0.12 := by
    rw [div_le_iff₀ hD]; nlinarith
  constructor
  · exact Real.log_nonneg (by linarith)
  · have := Real.log_le_sub_one_of_pos (show 0 < 1 + 3 * Real.log 2 / (2 * D) by linarith)
    linarith

/-- `C_{x₀,2}/log 2 > 0.08659`, against page 73. -/
theorem C_ratio_at_2 : (0.08659 : ℝ) < Cxt 2.16e20 2 / Real.log 2 := by
  have ⟨_, d2⟩ := den_bounds
  have d1 := den_bounds.1
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  unfold Cxt
  rw [log8]
  set D := Real.log (9 * (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / (2.004 * 2))
  have hD : 0 < 2 * D := by linarith
  set u := 3 * Real.log 2 / (2 * D) with hu
  have u_lo : 0.063 < u := by rw [hu, lt_div_iff₀ hD]; nlinarith
  -- exp 0.06003 = (exp 0.030015)² ≤ (1/(1 - 0.030015))² < 1.063
  have hv : Real.exp 0.06003 ≤ 1 + u := by
    have e2 : Real.exp 0.06003 = Real.exp 0.030015 * Real.exp 0.030015 := by
      rw [← Real.exp_add]; norm_num
    have b := exp_le_inv_one_sub 0.030015 (by norm_num)
    have b' : Real.exp 0.030015 ≤ 1.031 := by
      calc Real.exp 0.030015 ≤ 1 / (1 - 0.030015) := b
        _ ≤ 1.031 := by norm_num
    have p := Real.exp_pos 0.030015
    rw [e2]; nlinarith
  have hlog : 0.06003 ≤ Real.log (1 + u) := (Real.le_log_iff_exp_le (by linarith)).mpr hv
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

/-- The printed line 4 of page 73 fails at t = 2, for every `C` in [0, 0.12], so in
particular at `C = C_{x₀,2}`. -/
theorem printed_line4_fails_C (C : ℝ) (h0 : 0 ≤ C) (h1 : C ≤ 0.12) :
    printedRhs C (Real.log 2) < lhs C (Real.log 2) := by
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  unfold lhs printedRhs
  rw [h4, ← Real.sqrt_mul (by nlinarith)]
  have hP : 0 ≤ 0.27125 * C * (Real.log 2 + 0.002) + 0.4141 * Real.log 2 + 0.49911 := by
    nlinarith
  rw [Real.lt_sqrt hP]
  have hC : 0.27125 * C * (Real.log 2 + 0.002) ≤ 0.023 := by nlinarith
  have hA : 1.5 * Real.log 2 ≤ C * (Real.log 2 + 0.002) + (2 * Real.log 2 + Real.log 2) / 2 := by
    nlinarith
  have hB : 0 < 0.30214 * Real.log 2 + 0.67506 := by nlinarith
  have hAB : 1.5 * Real.log 2 * (0.30214 * Real.log 2 + 0.67506) ≤
      (C * (Real.log 2 + 0.002) + (2 * Real.log 2 + Real.log 2) / 2) *
        (0.30214 * Real.log 2 + 0.67506) := mul_le_mul_of_nonneg_right hA hB.le
  nlinarith

/-- The printed final inequality of page 73, line 4, is false at x = x₀ and t = δ₀q = 2. -/
theorem printed_line4_fails :
    printedRhs (Cxt 2.16e20 2) (Real.log 2) < lhs (Cxt 2.16e20 2) (Real.log 2) :=
  printed_line4_fails_C _ C_x0_2.1 C_x0_2.2

end LeanLab.HelfgottArcs.MinorQAMGM
