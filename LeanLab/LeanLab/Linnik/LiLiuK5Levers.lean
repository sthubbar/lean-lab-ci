/-
U-1112, T2 FRONTIER, I-0083. The K = 5 unconditional lever map in the setup of
Li-Liu, arXiv 2610.15784 v1, Section 7, read in Claude in Chrome 2026-10-19.

Plain math. Section 7 proves K = 5 under GRH from criterion (65)
  wᵀAw + τ² vᵀAv + D log 2/4 + H((C₁-2)/2 C₀R₀ + log 2/4) < 2τ(1-c)(1-a-b),
where log 2/4 comes from R₁,G(0)/(2NL) ≥ log 2/4 with the GRH arcs, P = N^{1/2}.
Section 6 uses the unconditional arcs of (24), N^{11/25} ≤ P ≤ N^{4/9-1/450}; its criterion (58)
carries 11 log 2/50 on the D term and 7 log 2/25 on the H term, that is (p/2) log 2 and
((1-p)/2) log 2 at p = 11/25. Model, stated as such: the K = 5 two-function argument with the
Section 6 arc constants. Then

1. `k5_uncond_criterion`: at the paper's own a = 1/4, b = 1/16, c = 1/8, τ = 2 and D_{25/32},
   criterion (65) with the unconditional arc constants still holds, from C₀R₀ < 1.279,
   C₁ = 6.7814, the tighter region bound `region67_tight` and the exact quadratic form.
2. `k5_exponent_ok_at_GRH`: the exceptional-set condition (2σ-1) log 2 < I(25/32) holds at σ = 3/4.
3. `minor_level_barrier`: with an MPR shape bound N P^{-1/2} + N^σ and P ≤ N^{4/9-1/450}, the
   exponent is at least 1 - p/2 > 0.7788, so the condition of item 2 needs P near N^{1/2}.
   Python, numerics/k5_levers_U1112.out: the condition needs σ < 0.7510 at λ = 25/32 and
   σ < 0.7524 at the best λ ≈ 0.7831 with the parameters optimised; MPR gives 19/24 ≈ 0.7917.

So inside Li-Liu's method, GRH enters K = 5 only through the minor arc exponent, and the
unconditional route needs both a minor arc exponent about 0.752 and major arcs to about
N^{0.494}. Numeric facts only; the analytic steps stay with the paper. KNOWN status pending,
see IDEAS I-0083. AI-written Lean code, Claude, 2026-10-19. Goldbach is open.
-/
import Mathlib
import LeanLab.Linnik.LiLiu2026

namespace LeanLab.Linnik.LiLiuK5

open LeanLab.Linnik.LiLiu

/-- The exact quadratic form of Section 7's parameters with the (23) tails, below 0.1826. -/
theorem wAw_tail_tight :
    (51822763867 / 349920000000 : ℚ) + (0.254 / 8 + 0.077) ^ 2
      + 4 * (0.254 / 16 + 0.077 / 4 + 0.04) ^ 2 < 1826 / 10000 := by
  norm_num

/-- (67) tightened: |z - 1/8|² + 4|Q(z)|² < 0.681 on D_{25/32}; the maximum is 0.680557. -/
theorem region67_tight (z : ℂ) (hz : z ∈ Dl (25 / 32)) :
    Complex.normSq (z - 1 / 8) + 4 * Complex.normSq (z ^ 2 - z / 4 - 1 / 16) < 681 / 1000 := by
  obtain ⟨hx2, hD, hx⟩ := mem_Dl_poly beta2532_le (by norm_num) (by unfold rl; positivity) hz
  rw [normSq_Q, normSq_sub8]
  have hr : rl (25 / 32) = 625 / 2048 := by unfold rl; norm_num
  rw [hr] at hD
  set x := z.re; set u := Complex.normSq z
  have hp : 0 ≤ (u - x^2) * (625/2048 - u * (1 + 625/2048 - x)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hp, sq_nonneg (x - 726/1000), sq_nonneg (x+1/2), sq_nonneg u,
    mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hx)]

/-- Criterion (65) with the unconditional arc constants of Section 6, p = 11/25:
D = 1/32 carries (11/50) log 2 and H carries (7/25) log 2. The right side is
2τ(1 - c)(1 - a - b) = 77/32. CONDITIONAL in the lab's sense on the cited C₀R₀ < 1.279. -/
theorem k5_uncond_criterion {CR H WA : ℝ} (hCR0 : 0 ≤ CR) (hCR : CR < 1.279) (hH0 : 0 ≤ H)
    (hH : H < 681 / 1000) (hWA : WA < 1826 / 10000) :
    WA + 1 / 32 * (11 * Real.log 2 / 50) + H * ((6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25)
      < 2 * 2 * (1 - 1/8) * (1 - 1/4 - 1/16) := by
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : (6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25 < 3.2519 := by nlinarith
  have hX0 : 0 ≤ (6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25 := by positivity
  have : H * ((6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25) ≤ 681 / 1000 * 3.2519 :=
    mul_le_mul hH.le hX.le hX0 (by norm_num)
  nlinarith

/-- The printed GRH rounding 41/60 is too coarse for the unconditional constants:
with H = 41/60 and WA = 37/200, the left side of `k5_uncond_criterion` exceeds 77/32 at
C₀R₀ = 1.2784. So the tightening in `region67_tight` is needed. -/
theorem printed_rounding_too_coarse :
    2 * 2 * (1 - 1/8 : ℝ) * (1 - 1/4 - 1/16) <
      37 / 200 + 1 / 32 * (11 * Real.log 2 / 50)
        + 41 / 60 * ((6.7814 - 2) / 2 * 1.2784 + 7 * Real.log 2 / 25) := by
  have hl : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  nlinarith

/-- The exceptional set condition of (55) at σ = 3/4 and λ = 25/32: (2σ - 1) log 2 < I(25/32). -/
theorem k5_exponent_ok_at_GRH : (2 * (3 / 4 : ℝ) - 1) * Real.log 2 < Ilam (25 / 32) := by
  have h1 := gamma5.1
  have h2 := I2532
  linarith

/-- MPR shape barrier: with P = N^p and p ≤ 4/9 - 1/450, the minor arc term N P^{-1/2}
has exponent 1 - p/2 > 0.7788, above the 0.7510 that λ = 25/32 allows. -/
theorem minor_level_barrier (p : ℝ) (hp : p ≤ 4 / 9 - 1 / 450) : (0.7788 : ℝ) < 1 - p / 2 := by
  linarith

/-- With σ ≥ 0.7788 the condition (2σ - 1) log 2 < ρ needs ρ > 0.386, above 347/1000. -/
theorem barrier_rho (σ : ℝ) (hσ : 0.7788 ≤ σ) : (0.386 : ℝ) < (2 * σ - 1) * Real.log 2 := by
  have hl : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  nlinarith

/-- Vacuity: the hypotheses of `k5_uncond_criterion` hold together, at the region's maximum
point value 0.6806 and the exact form value 0.18253. -/
theorem vacuity : ∃ CR H WA : ℝ, 0 ≤ CR ∧ CR < 1.279 ∧ 0 ≤ H ∧ H < 681 / 1000 ∧
    WA < 1826 / 10000 :=
  ⟨1.2784421041, 0.6806, 0.18253, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end LeanLab.Linnik.LiLiuK5
