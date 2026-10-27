/-
P0069 Baker, Harman, Pintz 1997, Lemma 29, the elementary inequality of its proof, page 44, read
from the page images papers/P0069-original.pdf. Unit U-5157, CLOUD 20261019T0213Z-cloud14.

With `w = 1/2 + it`, `(1 + z)^w = exp(w L)`, `L = log(1 + z)`, and `J_y = [y, y + yz]` with
`z ≤ qQ/Y = 1/T₂`, `J_y` and `z` from Section 2, `T₂ = Y/qQ` from page 43.
PROVED: `exp_sub_one_le`, `|exp(wL) - 1| ≤ |w| L e^{L/2}`, from `exp(wL) - 1 = w ∫₀^L e^{wu} du`;
`exp_sub_one_le'`, `|exp(wL) - 1| ≤ e^{L/2} + 1`; `lemma29_ineq`, for `0 ≤ z ≤ 1`, `z ≤ 1/T₂`,
`|(1 + z)^w - 1|²/|w|² ≤ 9/(T₂² + t²)`, the page's `≪ 1/(T₂² + t²)`. MATCH.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma29
open Complex

theorem exp_sub_one_le {w : ℂ} (hw : w.re = 1 / 2) {L : ℝ} (hL : 0 ≤ L) :
    ‖Complex.exp (w * L) - 1‖ ≤ ‖w‖ * L * Real.exp (L / 2) := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  have hint := integral_exp_mul_complex (a := 0) (b := L) hw0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at hint
  have heq : Complex.exp (w * L) - 1 = w * ∫ x in (0 : ℝ)..L, Complex.exp (w * x) := by
    rw [hint]; field_simp
  rw [heq, norm_mul, mul_assoc]
  gcongr
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) L, ‖Complex.exp (w * x)‖ ≤ Real.exp (L / 2) := by
    intro x hx
    rw [Set.uIoc_of_le hL] at hx
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp [Complex.mul_re, hw]
    linarith [hx.2]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg hL] at this
  linarith

theorem exp_sub_one_le' {w : ℂ} (hw : w.re = 1 / 2) (L : ℝ) :
    ‖Complex.exp (w * L) - 1‖ ≤ Real.exp (L / 2) + 1 := by
  calc ‖Complex.exp (w * L) - 1‖ ≤ ‖Complex.exp (w * L)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = Real.exp (L / 2) + 1 := by
      rw [Complex.norm_exp]; simp [Complex.mul_re, hw]; ring_nf

theorem lemma29_ineq {t z T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hT : 0 < T) (hzT : z ≤ 1 / T) :
    ‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
        ‖(1 / 2 + t * I : ℂ)‖ ^ 2 ≤ 9 / (T ^ 2 + t ^ 2) := by
  set w : ℂ := 1 / 2 + t * I
  have hwre : w.re = 1 / 2 := by simp [w]
  have hw2 : ‖w‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [w]; ring
  set L := Real.log (1 + z)
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLz : L ≤ z := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + z by linarith); linarith
  have heL : Real.exp (L / 2) ≤ 3 / 2 := by
    have h1 : Real.exp L = 1 + z := Real.exp_log (by linarith)
    have h2 : Real.exp (L / 2) ^ 2 = Real.exp L := by rw [← Real.exp_nat_mul]; ring_nf
    nlinarith [Real.exp_pos (L / 2)]
  set E := ‖Complex.exp (w * L) - 1‖
  have hE0 : 0 ≤ E := norm_nonneg _
  have hE1 : E ≤ ‖w‖ * L * Real.exp (L / 2) := exp_sub_one_le hwre hL0
  have hE2 : E ≤ Real.exp (L / 2) + 1 := exp_sub_one_le' hwre L
  have hwpos : 0 < ‖w‖ ^ 2 := by rw [hw2]; positivity
  have hnw : 0 ≤ ‖w‖ := norm_nonneg _
  -- `E ≤ ‖w‖ z (3/2)` and `E ≤ 5/2`
  have hA : E ≤ ‖w‖ * z * (3 / 2) := by
    calc E ≤ ‖w‖ * L * Real.exp (L / 2) := hE1
      _ ≤ ‖w‖ * z * (3 / 2) := by gcongr
  have hB : E ≤ 5 / 2 := by linarith
  have hQ1 : E ^ 2 / ‖w‖ ^ 2 ≤ 9 / 4 * z ^ 2 := by
    rw [div_le_iff₀ hwpos]; nlinarith [mul_nonneg hnw hz]
  have hQ2 : E ^ 2 / ‖w‖ ^ 2 ≤ 25 / 4 / ‖w‖ ^ 2 := by
    apply div_le_div_of_nonneg_right _ hwpos.le; nlinarith
  set Q := E ^ 2 / ‖w‖ ^ 2
  have hTz : z * T ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hzT hT.le
    rwa [one_div, inv_mul_cancel₀ hT.ne'] at this
  have h1 : Q * T ^ 2 ≤ 9 / 4 := by
    have : z ^ 2 * T ^ 2 ≤ 1 := by nlinarith [mul_nonneg hz hT.le]
    nlinarith [sq_nonneg T]
  have h2 : Q * t ^ 2 ≤ 25 / 4 := by
    rw [hw2] at hQ2
    have hp : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
    have : 25 / 4 / (1 / 4 + t ^ 2) * t ^ 2 ≤ 25 / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hp]; nlinarith
    nlinarith [sq_nonneg t]
  have hden : 0 < T ^ 2 + t ^ 2 := by positivity
  rw [le_div_iff₀ hden]; nlinarith

end LeanLab.BHP1997.Lemma29
