/-
P0001 Helfgott 2013, arXiv 1312.7748v2, Section 7.3, page 65: the two steps the U-5103 VERIFY
named as not yet in Lean.
- "F(r) is increasing for r ≥ 27", with `F(r) = e^γ log log r + 2.50637/log log r`, used for
  `F(r₁) ≤ F(y^{4/15})`, `r₁ = (3/8) y^{4/15}`, in (7.40);
- the first-to-second-line algebra of (7.36) and (7.37).
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is Helfgott's theorem.
-/
import Mathlib
import LeanLab.Helfgott2013.SectionSevenE

open Real Finset

noncomputable section
namespace LeanLab.Helfgott2013.SectionSevenF

open LeanLab.Helfgott2013.GammaFine LeanLab.Helfgott2013.SectionSevenC
  LeanLab.Helfgott2013.SectionSevenD

/-- `F(r) = e^γ log log r + 2.50637 / log log r`, page 64. -/
def F (r : ℝ) : ℝ := exp eulerMascheroniConstant * log (log r) + 2.50637 / log (log r)

/-- `log log 27 ≥ 1.19`. -/
theorem lll27 : (1.19 : ℝ) ≤ log (log 27) := by
  have h27 : log (27 : ℝ) = 3 * log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, log_pow]; push_cast; ring
  have h3 := log3_bounds
  have he : exp (1.19 : ℝ) ≤ 3.2958 := by
    have hb := Real.exp_bound' (x := (0.19 : ℝ)) (by norm_num) (by norm_num) (n := 8)
      (by norm_num)
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have e : exp (1.19 : ℝ) = exp 1 * exp 0.19 := by rw [← exp_add]; norm_num
    have := Real.exp_one_lt_d9
    rw [e]; nlinarith [exp_pos (1 : ℝ), exp_pos (0.19 : ℝ)]
  rw [le_log_iff_exp_le (by rw [h27]; linarith), h27]
  linarith

/-- **Page 65: `F` is increasing for `r ≥ 27`.** With `u = log log r`, `F = a u + b/u` and
`F(s) - F(r) = (v - u)(a - b/(uv)) ≥ 0` because `u v ≥ 1.19² > b/a`. MATCHES. -/
theorem F_mono {r s : ℝ} (hr : 27 ≤ r) (hrs : r ≤ s) : F r ≤ F s := by
  have hu := lll27
  have hl27 : log (log (27 : ℝ)) ≤ log (log r) :=
    log_le_log (log_pos (by norm_num)) (log_le_log (by norm_num) hr)
  have hlr : 1 < log r := by
    have : (3 : ℝ) < log 27 := by
      rw [show (27 : ℝ) = 3 ^ 3 by norm_num, log_pow]; push_cast
      have := log3_bounds; linarith
    have := log_le_log (by norm_num) hr; linarith
  have huv : log (log r) ≤ log (log s) :=
    log_le_log (by linarith) (log_le_log (by linarith) hrs)
  set u := log (log r)
  set v := log (log s)
  have hu0 : 1.19 ≤ u := le_trans hu hl27
  have hv0 : 1.19 ≤ v := le_trans hu0 huv
  have ha := exp_gamma_gt
  unfold F
  have key : 2.50637 / u - 2.50637 / v ≤ exp eulerMascheroniConstant * (v - u) := by
    have e : 2.50637 / u - 2.50637 / v = 2.50637 * (v - u) / (u * v) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have huv' : 1.4161 ≤ u * v := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 huv) (sub_nonneg.2 huv'),
      mul_nonneg (sub_nonneg.2 huv) (by linarith : (0 : ℝ) ≤ exp eulerMascheroniConstant - 1.7810699)]
  nlinarith

/-- (7.40), first step: `F(r₁) ≤ F(y^{4/15})` with `r₁ = (3/8) y^{4/15}`, for `y ≥ 10²⁵`. -/
theorem F_r1_le {y : ℝ} (hy : 1e25 ≤ y) :
    F (3 / 8 * y ^ (4 / 15 : ℝ)) ≤ F (y ^ (4 / 15 : ℝ)) := by
  have hy0 : 0 < y := by linarith
  have hp : (1e5 : ℝ) ≤ y ^ (4 / 15 : ℝ) := by
    have h1 : (1e5 : ℝ) = (1e75 : ℝ) ^ (1 / 15 : ℝ) := by
      rw [show (1e75 : ℝ) = 1e5 ^ (15 : ℕ) by norm_num, ← rpow_natCast,
        ← rpow_mul (by norm_num)]; norm_num
    have h2 : (1e75 : ℝ) ≤ y ^ (4 : ℕ) := by
      calc (1e75 : ℝ) ≤ (1e25 : ℝ) ^ (4 : ℕ) := by norm_num
        _ ≤ y ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hy 4
    rw [h1, show (4 / 15 : ℝ) = 4 * (1 / 15) by norm_num, rpow_mul hy0.le]
    rw [show y ^ (4 : ℝ) = y ^ (4 : ℕ) by norm_cast]
    exact rpow_le_rpow (by norm_num) h2 (by norm_num)
  exact F_mono (by linarith) (by linarith)

/-- (7.36), line 1 to line 2: for `y > 0`, `log(8 · (3/8) y^{4/15}) = (4/15) log y + log 3` and
`log(9 y^{1/3}/(2.004 · (3/4) y^{4/15})) = (1/3 - 4/15) log y + log(9/(2.004 · 3/4))`. MATCHES. -/
theorem eq736 {y : ℝ} (hy : 0 < y) :
    log (8 * (3 / 8 * y ^ (4 / 15 : ℝ))) = 4 / 15 * log y + log 3 ∧
    log (9 * y ^ (1 / 3 : ℝ) / (2.004 * (3 / 4 * y ^ (4 / 15 : ℝ)))) =
      (1 / 3 - 4 / 15) * log y + log (9 / (2.004 * (3 / 4))) := by
  constructor
  · rw [show 8 * (3 / 8 * y ^ (4 / 15 : ℝ)) = 3 * y ^ (4 / 15 : ℝ) by ring,
      log_mul (by norm_num) (by positivity), log_rpow hy]; ring
  · have e1 : log (y ^ (1 / 3 : ℝ)) = 1 / 3 * log y := log_rpow hy _
    have e2 : log (y ^ (4 / 15 : ℝ)) = 4 / 15 * log y := log_rpow hy _
    rw [show 9 * y ^ (1 / 3 : ℝ) / (2.004 * (3 / 4 * y ^ (4 / 15 : ℝ))) =
        9 / (2.004 * (3 / 4)) * y ^ (1 / 3 : ℝ) / y ^ (4 / 15 : ℝ) by field_simp,
      log_div (by positivity) (by positivity), log_mul (by norm_num) (by positivity), e1, e2]
    ring

/-- (7.37), line 1 to line 2, with `K = (log y)/2`, `y > 1`: twice the logarithm in the
denominator is `(2/15) log y - (2/3) log log y + 2 log(9 · 2^{1/3}/(2.004 · 3/4))`. MATCHES. -/
theorem eq737_line12 {y : ℝ} (hy : 1 < y) :
    2 * log (9 * (y / (log y / 2)) ^ (1 / 3 : ℝ) / (2.004 * (3 / 4 * y ^ (4 / 15 : ℝ)))) =
      2 / 15 * log y - 2 / 3 * log (log y) +
        2 * log (9 * 2 ^ (1 / 3 : ℝ) / (2.004 * (3 / 4))) := by
  have hy0 : 0 < y := by linarith
  have hl : 0 < log y := log_pos hy
  have hz : 0 < y / (log y / 2) := by positivity
  have e1 : log ((y / (log y / 2)) ^ (1 / 3 : ℝ)) = 1 / 3 * (log y - (log (log y) - log 2)) := by
    rw [log_rpow hz, log_div hy0.ne' (by positivity), log_div hl.ne' (by norm_num)]
  have e2 : log (y ^ (4 / 15 : ℝ)) = 4 / 15 * log y := log_rpow hy0 _
  have e3 : log ((2 : ℝ) ^ (1 / 3 : ℝ)) = 1 / 3 * log 2 := log_rpow (by norm_num) _
  rw [show 9 * (y / (log y / 2)) ^ (1 / 3 : ℝ) / (2.004 * (3 / 4 * y ^ (4 / 15 : ℝ))) =
      9 / (2.004 * (3 / 4)) * (y / (log y / 2)) ^ (1 / 3 : ℝ) / y ^ (4 / 15 : ℝ) by field_simp,
    log_div (by positivity) (by positivity), log_mul (by norm_num) (by positivity), e1, e2,
    show 9 * (2 : ℝ) ^ (1 / 3 : ℝ) / (2.004 * (3 / 4)) = 9 / (2.004 * (3 / 4)) * 2 ^ (1 / 3 : ℝ) by
      ring,
    log_mul (by norm_num) (by positivity), e3]
  ring

end LeanLab.Helfgott2013.SectionSevenF
