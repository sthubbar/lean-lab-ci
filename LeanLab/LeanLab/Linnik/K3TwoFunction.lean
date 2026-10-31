/-
U-1138, T3 MOONSHOT, R-0015, the Linnik descent: K = 3 by Li-Liu's two-function trick.
Run 20261020T0103Z-16649.

Plain math. Li-Liu arXiv 2610.15784 v1 Section 7, read in Claude in Chrome 2026-10-20, proves
K = 5 = 2 + 3 under GRH by pairing g₂(n) g₃(N - n), F₂(z) = z² - cLz, F₃(z) = z³ - aLz² - bL²z,
Cauchy-Schwarz with weight τ, giving criterion (65)
  wᵀAw + τ² vᵀAv + D log 2/4 + H((C₁-2)/2 C₀R₀ + log 2/4) < 2τ(1-c)(1-a-b),
w = (-c, 1, 0), v = (-b, -a, 1), H = max_{D_{25/32}} (|z - c|² + τ²|Q(z)|²), D = c² + τ²b².
The K = 3 = 1 + 2 analogue, the lab's MODEL, pairs f₁ = r'₁, F₁(z) = z, with f₂ = r'₂ - cL r'₁:
  wᵀAw + τ² vᵀAv + D (p/2) log 2 + H((C₁-2)/2 C₀R₀ + ((1-p)/2) log 2) < 2τ(1-c),
w = (1, 0), v = (-c, 1), H = max_{D_λ} (1 + τ²|z - c|²), D = 1 + τ²c².

- `quad_le`: 2bτ ≤ k + aτ² when a > 0 and b² ≤ ak.
- `k3_fails`: for every c, every τ > 0, every p in [0, 1/2], λ ≥ 0.7799 through the two real
  points of D_λ, KLadder.mem_pts, the K = 3 criterion fails once C₁ ≥ 4 and C₀R₀ ≥ 1.27,
  given only wᵀAw ≥ 0.2146 and vᵀAv ≥ 0, both from A being a sum of Gram matrices.
- `k3_fails_at_lambda`: the same with H bounded through `mem_pts` directly.

So K = 3 by this route needs C₁ below the sieve parity floor 4: even Elliott-Halberstam
does not give it. Python numerics/k3_two_function_U1132.py: K = 3 needs C₁ < 3.483 with
GRH arcs and C₁ < 3.298 with the unconditional arcs, against K = 4 at 4.722 and 4.137, I-0084.
With K = 2 failing from C₁ ≥ 2.7, KLadder.k2_fails, the ladder reads: K = 4 is the lowest K
this method reaches with any upper bound sieve, and K ≤ 3 needs prime-pair information beyond
the parity barrier. A barrier map. AI-written Lean code, Claude, 2026-10-20. Goldbach is open.
-/
import Mathlib
import LeanLab.Linnik.KLadder

namespace LeanLab.Linnik.K3TwoFunction

open LeanLab.Linnik.LiLiu

/-- The one-variable quadratic step. -/
theorem quad_le {a b k τ : ℝ} (ha : 0 < a) (h : b ^ 2 ≤ a * k) : 2 * b * τ ≤ k + a * τ ^ 2 := by
  have h1 : 0 ≤ a * (k + a * τ ^ 2 - 2 * b * τ) := by nlinarith [sq_nonneg (a * τ - b)]
  have h2 : 0 ≤ k + a * τ ^ 2 - 2 * b * τ := by
    by_contra hneg; rw [not_le] at hneg; nlinarith
  linarith

/-- The core step: with X ≥ 1.443, m ≥ 0.326, b² ≤ 2.391 m and H ≥ 1 + τ² m,
2bτ ≤ A₁₁ + rest + H X for any rest ≥ 0. -/
theorem core {τ X m A11 rest H b : ℝ} (hX : 1.443 ≤ X) (hm : 0.326 ≤ m) (hb : b ^ 2 ≤ 2.391 * m)
    (hH : 1 + τ ^ 2 * m ≤ H) (hA : 0.2146 ≤ A11) (hrest : 0 ≤ rest) :
    2 * b * τ ≤ A11 + rest + H * X := by
  have hk : (2.391 : ℝ) ≤ (0.2146 + X) * X := by nlinarith
  have hk2 : b ^ 2 ≤ (X * m) * (0.2146 + X) := by
    have : 2.391 * m ≤ ((0.2146 + X) * X) * m := mul_le_mul_of_nonneg_right hk (by linarith)
    nlinarith
  have hq := quad_le (τ := τ) (mul_pos (by linarith) (by linarith)) hk2
  have hHX : (1 + τ ^ 2 * m) * X ≤ H * X := mul_le_mul_of_nonneg_right hH (by linarith)
  nlinarith

/-- K = 3 fails once C₁ ≥ 4: whatever c and τ > 0, the left side of the criterion is at least
2τ(1 - c), given H ≥ 1 + τ²(0.723 - c)² and H ≥ 1 + τ²(-0.419 - c)², the two real points. -/
theorem k3_fails {c τ A11 VA D H CR C1 p : ℝ} (hτ : 0 < τ) (hA : 0.2146 ≤ A11) (hVA : 0 ≤ VA)
    (hD : 0 ≤ D) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hCR : 1.27 ≤ CR) (hC1 : 4 ≤ C1)
    (h1 : 1 + τ ^ 2 * (0.723 - c) ^ 2 ≤ H) (h2 : 1 + τ ^ 2 * (-0.419 - c) ^ 2 ≤ H) :
    2 * τ * (1 - c) ≤ A11 + τ ^ 2 * VA + D * (p / 2 * Real.log 2)
      + H * ((C1 - 2) / 2 * CR + (1 - p) / 2 * Real.log 2) := by
  have hl : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl0 : 0 < Real.log 2 := by linarith
  have hX : 1.443 ≤ (C1 - 2) / 2 * CR + (1 - p) / 2 * Real.log 2 := by
    have : (1 : ℝ) * 1.27 ≤ (C1 - 2) / 2 * CR := by
      apply mul_le_mul (by linarith) hCR (by norm_num) (by linarith)
    have : (1 / 4 : ℝ) * 0.6931471803 ≤ (1 - p) / 2 * Real.log 2 := by
      apply mul_le_mul (by linarith) hl.le (by norm_num) (by linarith)
    linarith
  have hrest : 0 ≤ τ ^ 2 * VA + D * (p / 2 * Real.log 2) :=
    add_nonneg (mul_nonneg (sq_nonneg _) hVA) (mul_nonneg hD (by positivity))
  have key : 2 * (1 - c) * τ ≤ A11 + (τ ^ 2 * VA + D * (p / 2 * Real.log 2))
      + H * ((C1 - 2) / 2 * CR + (1 - p) / 2 * Real.log 2) := by
    rcases le_or_gt c 0.152 with hc | hc
    · have hm : (0.326 : ℝ) ≤ (0.723 - c) ^ 2 := by nlinarith
      have hb : (1 - c) ^ 2 ≤ 2.391 * (0.723 - c) ^ 2 := by
        have hp1 : 0 ≤ 1.391 * c ^ 2 - 1.457386 * c + 0.249845039 := by nlinarith [sq_nonneg c]
        have e : 2.391 * (0.723 - c) ^ 2 - (1 - c) ^ 2 = 1.391 * c ^ 2 - 1.457386 * c + 0.249845039 := by ring
        linarith
      exact core hX hm hb h1 hA hrest
    · have hm : (0.326 : ℝ) ≤ (-0.419 - c) ^ 2 := by nlinarith
      have hb : (1 - c) ^ 2 ≤ 2.391 * (-0.419 - c) ^ 2 := by
        have hp1 : 0 ≤ 1.391 * c ^ 2 + 4.003658 * c - 0.580233649 := by nlinarith [sq_nonneg c]
        have e : 2.391 * (-0.419 - c) ^ 2 - (1 - c) ^ 2 = 1.391 * c ^ 2 + 4.003658 * c - 0.580233649 := by ring
        linarith
      exact core hX hm hb h2 hA hrest
  linarith

/-- The same with H any upper bound of 1 + τ²|z - c|² over D_λ, λ in [0.7799, 1). -/
theorem k3_fails_at_lambda {l c τ A11 VA D H CR C1 p : ℝ} (hl : 0.7799 ≤ l) (hl1 : l < 1)
    (hHmax : ∀ z ∈ Dl l, 1 + τ ^ 2 * Complex.normSq (z - c) ≤ H)
    (hτ : 0 < τ) (hA : 0.2146 ≤ A11) (hVA : 0 ≤ VA)
    (hD : 0 ≤ D) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hCR : 1.27 ≤ CR) (hC1 : 4 ≤ C1) :
    2 * τ * (1 - c) ≤ A11 + τ ^ 2 * VA + D * (p / 2 * Real.log 2)
      + H * ((C1 - 2) / 2 * CR + (1 - p) / 2 * Real.log 2) := by
  obtain ⟨m1, m2⟩ := LeanLab.Linnik.KLadder.mem_pts hl hl1
  have e : ∀ x : ℝ, Complex.normSq ((x : ℂ) - c) = (x - c) ^ 2 := by
    intro x; rw [← Complex.ofReal_sub, Complex.normSq_ofReal]; ring
  have h1 := hHmax _ m1; have h2 := hHmax _ m2
  rw [e] at h1 h2
  exact k3_fails hτ hA hVA hD hp0 hp hCR hC1 h1 h2

/-- Vacuity: the hypotheses of `k3_fails` hold at c = 0.15, τ = 1.5, C₁ = 4, C₀R₀ = 1.2784. -/
theorem vacuity : ∃ c τ H : ℝ, 0 < τ ∧ 1 + τ ^ 2 * (0.723 - c) ^ 2 ≤ H ∧
    1 + τ ^ 2 * (-0.419 - c) ^ 2 ≤ H :=
  ⟨0.15, 1.5, 2, by norm_num, by norm_num, by norm_num⟩

end LeanLab.Linnik.K3TwoFunction

