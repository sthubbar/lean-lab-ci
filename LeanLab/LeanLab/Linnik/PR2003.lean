/-
P0026 Pintz, Ruzsa 2003, On Linnik's approximation to Goldbach's problem I, Acta Arith. 109, read from
papers/P0026.pdf, the open IMPAN copy, unit U-5053. Theorem 1: under GRH, K = 7 powers of 2 suffice.
PROVED, the closing arithmetic with the paper's constants: `lemma10`, C₂ < 5.3636; `lemma11`, C₂₀ < 3.9095,
both for C₀ < 0.6602, R₀ < 1.94, C* = 3.9171; `eq102`, (10.2); `eq1015`, (10.15) √(1.0431 · 0.5323) ≤ 0.7452 < 1.
Corollaries 1 and 2, the large-deviation constants 0.7163435 and 0.7894008, recomputed in numerics/pr1_check.py.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Linnik.PR2003
open Real

theorem lemma10 {C0 R0 : ℝ} (h0 : 0 ≤ C0) (hC0 : C0 < 0.6602) (hR : 0 ≤ R0) (hR0 : R0 < 1.94) :
    C0 * R0 * 3.9171 + log 2 / 2 < 5.3636 := by
  have hl := log_two_lt_d9
  have : C0 * R0 ≤ 0.6602 * 1.94 := mul_le_mul hC0.le hR0.le hR (by norm_num)
  norm_num at hl ⊢; nlinarith

theorem lemma11 {C0 R0 : ℝ} (h0 : 0 ≤ C0) (hC0 : C0 < 0.6602) (hR : 0 ≤ R0) (hR0 : R0 < 1.94) :
    C0 * R0 * (3.9171 - 1) + log 2 / 4 < 3.9095 := by
  have hl := log_two_lt_d9
  have : C0 * R0 ≤ 0.6602 * 1.94 := mul_le_mul hC0.le hR0.le hR (by norm_num)
  norm_num at hl ⊢; nlinarith

theorem eq102 {A3 A4 : ℝ} (h3 : A3 < 0.0136) (h4 : A4 < 0.004) :
    A3 + 3.9095 * (1 - 0.283656 : ℝ) ^ 4 < 1.0431 ∧ A4 + 3.9095 * (1 - 0.283656 : ℝ) ^ 6 < 0.5323 := by
  constructor <;> norm_num <;> linarith

theorem eq1015 : √((1.0431 : ℝ) * 0.5323) ≤ 0.7452 ∧ (0.7452 : ℝ) < 1 := by
  refine ⟨?_, by norm_num⟩
  rw [sqrt_le_left (by norm_num)]; norm_num

end LeanLab.Linnik.PR2003
