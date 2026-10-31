/-
P0001 H. A. Helfgott, arXiv 1312.7748v2, Section 7.3, page 69: the bound
`f₀(r₀, y) ≤ 0.4153461 · √(2 I₁/√r₀) ≤ 0.069219` with `I₁ = 5.73827`, `r₀ = 150000`, from the
definition (6.31). The middle product is `0.0714978...`, so the printed `0.069219` is too
small. The book version, arXiv 1501.05438, (14.46) and the next display, prints
`≤ 0.071498` and redoes Section 7 with new constants; this is a known, corrected slip.
We prove the slip, and that with the corrected `0.071498` the v2 chain of Section 7 still
closes: the integral bound becomes `0.089197`, (7.46) `0.114210 x`, (7.47) `0.77962 x`,
(7.48) `0.97757 x²/κ`, and the odd prime part stays `≥ 0.0004 N² > 0` for `N ≥ 10^27`.
The v2 main theorem survives.

AI-written Lean code, Claude, 2026-10-18, cloud session 20261018T1720Z-cloud5.
Checked only by the Lean kernel. Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Helfgott2013.SectionSeven

namespace LeanLab.Helfgott2013
open Real

/-- `f₀` as defined in (6.31) with the bound 0.4153461 of (7.45) and `I₁ = 5.73827`. -/
noncomputable def f0val : ℝ := 0.4153461 * Real.sqrt (2 * 5.73827 / Real.sqrt 150000)

theorem sqrt_150000_bounds : (387.2983 : ℝ) ≤ Real.sqrt 150000 ∧ Real.sqrt 150000 ≤ 387.3 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- The slip: `0.4153461 · √(2 · 5.73827/√150000) > 0.069219`. -/
theorem f0_slip : (0.069219 : ℝ) < f0val := by
  obtain ⟨_, h2⟩ := sqrt_150000_bounds
  have hq : (0.1667 : ℝ) ^ 2 < 2 * 5.73827 / Real.sqrt 150000 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hs : (0.1667 : ℝ) < Real.sqrt (2 * 5.73827 / Real.sqrt 150000) :=
    Real.lt_sqrt_of_sq_lt hq
  unfold f0val; nlinarith

/-- The book's value: `0.4153461 · √(2 · 5.73827/√150000) ≤ 0.071498`. -/
theorem f0_book : f0val ≤ (0.071498 : ℝ) := by
  obtain ⟨h1, _⟩ := sqrt_150000_bounds
  have hq : 2 * 5.73827 / Real.sqrt 150000 ≤ (0.1721404 : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hs : Real.sqrt (2 * 5.73827 / Real.sqrt 150000) ≤ 0.1721404 :=
    (Real.sqrt_le_left (by norm_num)).mpr hq
  unfold f0val; nlinarith

/-- The v2 chain with `0.071498` in place of `0.069219`: `0.071498 + 0.016367 + 0.001332 ≤
0.089197`, `1.280418 · 0.089197 ≤ 0.114210`, `0.36155 + 0.30386 + 0.114210 ≤ 0.77962`. -/
theorem repaired_M : (0.071498 : ℝ) + 0.016367 + 0.001332 ≤ 0.089197 ∧
    (1.280418 : ℝ) * 0.089197 ≤ 0.114210 ∧ (0.36155 : ℝ) + 0.30386 + 0.114210 ≤ 0.77962 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The repaired (7.48): `(√(|ϕ|₁ (0.77962 + 3.5776 · 10^-4)) + √(1.0532 · 10^-11))² ≤ 0.97757`. -/
theorem repaired_minor :
    (Real.sqrt (Real.sqrt (π / 2) * (0.77962 + 3.5776e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
      (0.97757 : ℝ) := by
  have hs := sqrt_pi_half_lt
  have hs0 : 0 ≤ Real.sqrt (π / 2) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (Real.sqrt (π / 2) * (0.77962 + 3.5776e-4)) ≤ (0.988717 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have h2 : Real.sqrt 1.0532e-11 ≤ (3.2454e-6 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h0 : 0 ≤ Real.sqrt (Real.sqrt (π / 2) * (0.77962 + 3.5776e-4)) + Real.sqrt 1.0532e-11 :=
    by positivity
  have : (Real.sqrt (Real.sqrt (π / 2) * (0.77962 + 3.5776e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
      (0.988717 + 3.2454e-6) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
  have : ((0.988717 : ℝ) + 3.2454e-6) ^ 2 ≤ 0.97757 := by norm_num
  linarith

/-- The repaired last display: `1.058259 − 0.97757 ≥ 0.08068`, and for `N ≥ 10^27`, from a
total `T ≥ 0.08068 x²/κ` and `E ≤ 7.3306 N^{3/2} log N`, `T − E ≥ 0.0004 N² > 0`. -/
theorem repaired_chain {N T E : ℝ} (hN : 1e27 ≤ N)
    (hT : 0.08068 * xOf N ^ 2 / κ ≤ T) (hE : E ≤ 7.3306 * N ^ (3 / 2 : ℝ) * Real.log N) :
    (0.08068 : ℝ) ≤ 1.058259 - 0.97757 ∧ 0.0004 * N ^ 2 ≤ T - E ∧ 0 < T - E := by
  have hc : (0.0004041 : ℝ) ≤ 0.08068 * ratio ^ 2 / κ := by
    have h := coeff_ge
    unfold κ at h ⊢
    have hr : (0 : ℝ) ≤ ratio ^ 2 := sq_nonneg _
    have : 0.08068 * ratio ^ 2 / 49 = (0.08068 / 0.08433) * (0.08433 * ratio ^ 2 / 49) := by ring
    rw [this]
    calc (0.0004041 : ℝ) ≤ (0.08068 / 0.08433) * 0.00042248 := by norm_num
      _ ≤ _ := by gcongr
  have h1 : 0.0004041 * N ^ 2 ≤ 0.08068 * xOf N ^ 2 / κ := by
    have : 0.08068 * xOf N ^ 2 / κ = (0.08068 * ratio ^ 2 / κ) * N ^ 2 := by unfold xOf; ring
    rw [this]; exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have h2 := error_le hN
  have hN2 : 0 < N ^ 2 := by positivity
  refine ⟨by norm_num, ?_, ?_⟩ <;> nlinarith

end LeanLab.Helfgott2013
