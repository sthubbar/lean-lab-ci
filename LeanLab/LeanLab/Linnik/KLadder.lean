/-
U-1114, T3 MOONSHOT, R-0015: the Linnik descent, K powers of two down to K = 0.

Plain math. Li-Liu arXiv 2610.15784 v1, criterion (58), for one polynomial
F(z) = z^d + c_{d-1} z^{d-1} + ... + c_1 z, K = 2d powers, v_i the coefficient of z^i:
  vᵀAv + v₁² (p/2) log 2 + H((C₁-2)/2 C₀R₀ + ((1-p)/2) log 2) < F(1)²,  H = max_{D_λ} |F(z)/z|²,
with λ forced by the exceptional set step, I(λ) > (2σ - 1) log 2, so λ > 0.7799 even at the GRH
exponent σ = 3/4. C₁ is the upper sieve constant for prime pairs, normalised so that the
Hardy-Littlewood value is 2; an upper bound sieve alone cannot go below 4, twice the truth, by
Selberg's parity barrier.

- `k2_fails`: K = 2, F(z) = z, H = 1, fails for every p once C₁ ≥ 2.7, given A₁₁ ≥ 0.2146,
  which `Astar_diag` proves for the A_* part of A, and C₀R₀ ≥ 1.27. Since 2.7 < 4, K = 2 by this
  route needs a prime-pair upper bound below the parity floor of sieve methods.
- `k4_fails`: K = 4, F(z) = z² + c z, fails for every c once C₁ ≥ 5.21, using only the two real
  points 0.723 and -0.419 of D_λ, `mem_pts`, for λ ≥ 0.7799. JT's C₁ = 6.7814. Python
  numerics/kladder_U1114.out, all of D_λ and A_* kept: K = 4 needs C₁ < 4.786 under GRH and
  C₁ < 4.194 unconditionally, both above 4, so K = 4 is not blocked by parity in this model.
- K = 0 has no G factor at all: the minor arcs carry (1 - p) N log N of ∫|S|², against N, the
  L² barrier of R-0001. Not a Lean statement here.

AI-written Lean code, Claude, 2026-10-19. A barrier map, not progress on Goldbach, which is open.
-/
import Mathlib
import LeanLab.Linnik.LiLiu2026

namespace LeanLab.Linnik.KLadder

open LeanLab.Linnik.LiLiu

/-- K = 2: with F(z) = z, so v = (1), F(1) = 1, H = 1, the criterion cannot hold once C₁ ≥ 2.7. -/
theorem k2_fails {A11 CR C1 p : ℝ} (hA : 0.2146 ≤ A11) (hCR : 1.27 ≤ CR) (hC1 : 2.7 ≤ C1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 : ℝ) ≤ A11 + 1 ^ 2 * (p / 2 * Real.log 2) + 1 * ((C1 - 2) / 2 * CR + (1 - p) / 2 * Real.log 2) := by
  have hl : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have h1 : (0.35 : ℝ) * 1.27 ≤ (C1 - 2) / 2 * CR := by nlinarith
  nlinarith

/-- The A_* diagonal entry is a lower bound for A₁₁, since each A(q) is a Gram matrix;
here the A_* value itself, from `Astar_diag`, is 0.2146 or more. -/
theorem astar11_ge : (0.2146 : ℝ) ≤ (Astar 0 0 : ℝ) := by
  have h : ((0.2146 : ℚ) : ℝ) ≤ ((Astar 0 0 : ℚ) : ℝ) := Rat.cast_le.mpr Astar_diag.1.le
  have e : ((0.2146 : ℚ) : ℝ) = (0.2146 : ℝ) := by norm_num
  rw [e] at h; exact h

/-- Two real points of D_λ for every λ in [0.7799, 1). -/
theorem mem_pts {l : ℝ} (hl : 0.7799 ≤ l) (hl1 : l < 1) :
    ((0.723 : ℝ) : ℂ) ∈ Dl l ∧ ((-0.419 : ℝ) : ℂ) ∈ Dl l := by
  have hr : 0.30412 ≤ rl l := by unfold rl; nlinarith
  have hr1 : rl l < 1 := by unfold rl; nlinarith
  have hb : 0.723 ≤ betal l := by
    unfold betal
    have hs : 1.446 - rl l ≤ Real.sqrt (rl l ^ 2 + 4 * rl l) := by
      apply Real.le_sqrt_of_sq_le; nlinarith
    linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa using hb
  · simp only [Complex.normSq_ofReal, Complex.ofReal_re]
    rw [le_div_iff₀ (by linarith)]; nlinarith
  · simp only [Complex.ofReal_re]; linarith
  · simp only [Complex.normSq_ofReal, Complex.ofReal_re]
    rw [le_div_iff₀ (by linarith)]; nlinarith

/-- The one-variable step: for every real c, (1 + c)² ≤ 2.21 max((0.723 + c)², (c - 0.419)²). -/
theorem key_max (c H : ℝ) (h1 : (0.723 + c) ^ 2 ≤ H) (h2 : (-0.419 + c) ^ 2 ≤ H) :
    (1 + c) ^ 2 ≤ 2.21 * H := by
  rcases le_or_gt (-0.152) c with hc | hc
  · nlinarith [sq_nonneg (c + 0.152)]
  · nlinarith [sq_nonneg (c + 0.152)]

/-- K = 4: F(z) = z² + c z, Q(z) = z + c, v = (c, 1), F(1) = 1 + c. Whatever c, the criterion
fails once C₁ ≥ 5.21, with H only bounded below by the two real points of `mem_pts`
and the A and D terms only taken nonnegative. -/
theorem k4_fails {c H QA CR C1 p : ℝ} (hQA : 0 ≤ QA) (hCR : 1.27 ≤ CR) (hC1 : 5.21 ≤ C1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (h1 : (0.723 + c) ^ 2 ≤ H) (h2 : (-0.419 + c) ^ 2 ≤ H) :
    (1 + c) ^ 2 ≤ QA + c ^ 2 * (p / 2 * Real.log 2)
      + H * ((C1 - 2) / 2 * CR + (1 - p) / 2 * Real.log 2) := by
  have hl : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl0 : 0 < Real.log 2 := by linarith
  have hH : 0 ≤ H := le_trans (sq_nonneg _) h1
  have hk : (2.21 : ℝ) ≤ (C1 - 2) / 2 * CR + (1 - p) / 2 * Real.log 2 := by
    have : (3.21 / 2 : ℝ) * 1.27 ≤ (C1 - 2) / 2 * CR := by nlinarith
    nlinarith
  have hkey := key_max c H h1 h2
  have hD : 0 ≤ c ^ 2 * (p / 2 * Real.log 2) := by
    apply mul_nonneg (sq_nonneg _); apply mul_nonneg (by linarith) hl0.le
  have : 2.21 * H ≤ H * ((C1 - 2) / 2 * CR + (1 - p) / 2 * Real.log 2) := by nlinarith
  linarith

/-- Vacuity of `k4_fails`: its hypotheses hold at JT's C₁ = 6.7814, C₀R₀ = 1.2784, p = 1/2. -/
theorem vacuity : ∃ c H : ℝ, (0.723 + c) ^ 2 ≤ H ∧ (-0.419 + c) ^ 2 ≤ H ∧
    (1.27 : ℝ) ≤ 1.2784 ∧ (5.21 : ℝ) ≤ 6.7814 :=
  ⟨-0.152, 0.33, by norm_num, by norm_num, by norm_num, by norm_num⟩

end LeanLab.Linnik.KLadder
