/-
P0001 Helfgott 2013, arXiv 1312.7748v2, Section 7.3, page 64: (7.33), (7.34) and the
inputs `y/K ≥ 3.47435 · 10²³` and `log((log y)/2) ≥ 3.35976` for `y ≥ 10²⁵`, `K = (log y)/2`.
With SectionSevenC and SectionSevenD this puts every printed constant of (7.32) to (7.48)
in Lean, except the VNODE-LP integral behind (7.31).
Formulas read from the rendered page image of page 64.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is Helfgott's theorem.
-/
import Mathlib
import LeanLab.Helfgott2013.SectionSevenD

open Real Finset

noncomputable section
namespace LeanLab.Helfgott2013.SectionSevenE

open LeanLab.ChenExplicit.Gamma LeanLab.Helfgott2013.SectionSevenC
  LeanLab.Helfgott2013.SectionSevenD

theorem log_1e25 : log (1e25 : ℝ) = 25 * log 10 := by
  rw [show (1e25 : ℝ) = 10 ^ 25 by norm_num, log_pow]; push_cast; ring

/-- **Page 64: `y/K ≥ 3.47435 · 10²³` for `y ≥ 10²⁵`, `K = (log y)/2`.** MATCHES. -/
theorem yK_ge {y : ℝ} (hy : 1e25 ≤ y) : (3.47435e23 : ℝ) ≤ y / (log y / 2) := by
  have he : exp 1 ≤ (1e25 : ℝ) := by have := exp_one_lt_d9; linarith
  have hanti := Real.log_div_self_antitoneOn (Set.mem_setOf.2 he)
    (Set.mem_setOf.2 (le_trans he hy)) hy
  simp only at hanti
  have hy0 : 0 < y := by linarith
  have hly : 0 < log y := log_pos (by linarith)
  rw [log_1e25] at hanti
  have ht := t0_bounds
  rw [le_div_iff₀ (by positivity)]
  rw [div_le_div_iff₀ hy0 (by norm_num)] at hanti
  nlinarith

/-- **Page 64: `log((log y)/2) ≥ 3.35976` for `y ≥ 10²⁵`.** MATCHES. -/
theorem logK_ge {y : ℝ} (hy : 1e25 ≤ y) : (3.35976 : ℝ) ≤ log (log y / 2) := by
  have hy0 : 0 < y := by linarith
  have hly : (57.564627305 : ℝ) ≤ log y := by
    have := log_le_log (by norm_num) hy; rw [log_1e25] at this; linarith [t0_bounds.1]
  have h1 : log (57.564627305 / 2 : ℝ) ≤ log (log y / 2) := log_le_log (by norm_num) (by linarith)
  rw [log_via (by norm_num) (by norm_num : (57.564627305 / 2 : ℝ) < 32)] at h1
  rw [show log (32 : ℝ) = 5 * log 2 by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, log_pow]; push_cast; ring] at h1
  have hs := log_one_add_inv_le_sum (a := (57.564627305 / 2 : ℝ) / (32 - 57.564627305 / 2))
    (by norm_num) 4
  simp only [sum_range_succ, sum_range_zero] at hs
  norm_num at hs
  have := log_two_gt_d9
  norm_num at h1 ⊢
  linarith

/-- `log(9 z^{1/3} / (2.004 · 2 · 150000)) = 2 log 3 + (log z)/3 - 2 log 2 - log 1.002 - log 150000`. -/
theorem den_eq {z : ℝ} (hz : 0 < z) :
    log (9 * z ^ (1 / 3 : ℝ) / (2.004 * 2 * 150000)) =
      2 * log 3 + log z / 3 - 2 * log 2 - log 1.002 - log 150000 := by
  rw [log_div (by positivity) (by norm_num), log_mul (by norm_num) (by positivity),
    log_rpow hz, show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow,
    show (2.004 * 2 * 150000 : ℝ) = 2 ^ 2 * 1.002 * 150000 by norm_num,
    log_mul (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num), log_pow]
  push_cast; ring

/-- The common shape: `0.27125 log(1 + N/(2D)) + 0.41415 ≤ R` from `N ≤ N₀`, `D ≥ D₀ > 0`, and
`log(1 + N₀/(2D₀)) ≤ ℓ`. -/
theorem R_shape {N D N₀ D₀ ℓ R : ℝ} (hN0 : 0 ≤ N) (hN : N ≤ N₀) (hD0 : 0 < D₀) (hD : D₀ ≤ D)
    (hℓ : log (1 + N₀ / (2 * D₀)) ≤ ℓ) (hR : 0.27125 * ℓ + 0.41415 ≤ R) :
    0.27125 * log (1 + N / (2 * D)) + 0.41415 ≤ R := by
  have hq : N / (2 * D) ≤ N₀ / (2 * D₀) :=
    div_le_div₀ (by linarith) hN (by positivity) (by linarith)
  have hq0 : 0 ≤ N / (2 * D) := div_nonneg hN0 (by linarith)
  have := log_le_log (by linarith) (by linarith : 1 + N / (2 * D) ≤ 1 + N₀ / (2 * D₀))
  linarith

theorem num_bounds : log (8 * 150000 : ℝ) ≤ 13.9978322 ∧ 0 ≤ log (8 * 150000 : ℝ) := by
  have e : log (8 * 150000 : ℝ) = 3 * log 2 + log 150000 := by
    rw [log_mul (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
    push_cast; ring
  rw [e]
  have := log_two_lt_d9; have := log_two_gt_d9; have := log_r0_bounds
  constructor <;> linarith

/-- **(7.33): `R_{y,2r₀} ≤ 0.58341` for `y ≥ 10²⁵`.** MATCHES; value `0.5834039` at `10²⁵`. -/
theorem R733 {y : ℝ} (hy : 1e25 ≤ y) :
    0.27125 * log (1 + log (8 * 150000) / (2 * log (9 * y ^ (1 / 3 : ℝ) / (2.004 * 2 * 150000))))
      + 0.41415 ≤ (0.58341 : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hly : (57.564627305 : ℝ) ≤ log y := by
    have := log_le_log (by norm_num) hy; rw [log_1e25] at this; linarith [t0_bounds.1]
  have hN := num_bounds
  have hD : (8.0787506 : ℝ) ≤ log (9 * y ^ (1 / 3 : ℝ) / (2.004 * 2 * 150000)) := by
    rw [den_eq hy0]
    have := log3_bounds; have := log_two_lt_d9; have := l1002_bounds; have := log_r0_bounds
    linarith
  refine R_shape hN.2 hN.1 (by norm_num) hD (ℓ := 0.62399) ?_ (by norm_num)
  -- log(1 + 13.9978322/(2 · 8.0787506)) = log 2 - log(1 + 1/a)
  rw [log_via (by norm_num) (by norm_num : (1 + 13.9978322 / (2 * 8.0787506) : ℝ) < 2)]
  have hs := log_one_add_inv_ge_sum
    (a := (1 + 13.9978322 / (2 * 8.0787506) : ℝ) / (2 - (1 + 13.9978322 / (2 * 8.0787506))))
    (by norm_num) 2
  simp only [sum_range_succ, sum_range_zero] at hs
  norm_num at hs
  have := log_two_lt_d9
  norm_num
  linarith

/-- **(7.34): `R_{y/K,2r₀} ≤ 0.60295` when `y/K ≥ 3.47435 · 10²³`**, as page 64 uses it.
MATCHES; value `0.6029463` at the bound. -/
theorem R734 {z : ℝ} (hz : 3.47435e23 ≤ z) :
    0.27125 * log (1 + log (8 * 150000) / (2 * log (9 * z ^ (1 / 3 : ℝ) / (2.004 * 2 * 150000))))
      + 0.41415 ≤ (0.60295 : ℝ) := by
  have hz0 : 0 < z := by linarith
  have hlZ : (54.2048645 : ℝ) ≤ log z := by
    have h1 : log (3.47435e23 : ℝ) ≤ log z := log_le_log (by norm_num) hz
    have e : log (3.47435e23 : ℝ) = log 1e25 - log (10 ^ 7 / 347435) := by
      rw [← log_div (by norm_num) (by norm_num)]; norm_num
    rw [e, log_1e25] at h1
    have hU : log (10 ^ 7 / 347435 : ℝ) ≤ 3.3597628 := by
      rw [log_via (by norm_num) (by norm_num : (10 ^ 7 / 347435 : ℝ) < 32)]
      rw [show log (32 : ℝ) = 5 * log 2 by
        rw [show (32 : ℝ) = 2 ^ 5 by norm_num, log_pow]; push_cast; ring]
      have hs := log_one_add_inv_ge_sum
        (a := (10 ^ 7 / 347435 : ℝ) / (32 - 10 ^ 7 / 347435)) (by norm_num) 3
      simp only [sum_range_succ, sum_range_zero] at hs
      norm_num at hs
      have := log_two_lt_d9
      norm_num
      linarith
    have := t0_bounds.1
    linarith
  have hN := num_bounds
  have hD : (6.9588297 : ℝ) ≤ log (9 * z ^ (1 / 3 : ℝ) / (2.004 * 2 * 150000)) := by
    rw [den_eq hz0]
    have := log3_bounds; have := log_two_lt_d9; have := l1002_bounds; have := log_r0_bounds
    linarith
  refine R_shape hN.2 hN.1 (by norm_num) hD (ℓ := 0.69603) ?_ (by norm_num)
  rw [log_via (by norm_num) (by norm_num : (1 + 13.9978322 / (2 * 6.9588297) : ℝ) < 9 / 4)]
  rw [show log (9 / 4 : ℝ) = 2 * log (3 / 2) by
    rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, log_pow]; push_cast; ring]
  have hs := log_one_add_inv_ge_sum
    (a := (1 + 13.9978322 / (2 * 6.9588297) : ℝ) / (9 / 4 - (1 + 13.9978322 / (2 * 6.9588297))))
    (by norm_num) 2
  simp only [sum_range_succ, sum_range_zero] at hs
  norm_num at hs
  have := l32_hi
  norm_num
  linarith

end LeanLab.Helfgott2013.SectionSevenE
