/-
T2, unit U-1089, PC run 20261019T1803Z-6290. A barrier note on the bilinear Goldbach argument
under RH. I-5030 found that the 9.77 log² x floor of Bilinear64.lean can only be passed with a
LOCAL mean-square bound, over a window [y, κ y], sharper than the cumulative Theorem 2 of
Chirre-Hagen, arXiv 2512.23534v1. Their proof of Theorem 2 does pass through a local bound,
display (3.6), section 3:

  ∫_x^{κx} (ψ((1+δ)y) − ψ(y) − δy)² dy ≤ 𝒞(κ, λ, η) δ log²(ℓ/δ) x²,
  𝒞(κ, λ, η) = (1+η) · 2.0282/(√6 π) · (κ² + 1/λ²) · (λ³+1)/(λ−1) + 1.3·10⁻¹⁷ (1 + 1/η)(λ³ − 1/κ³)(λ+1)/λ².

This file proves that the main part of 𝒞 is at least 2.224 κ² for every κ > 1, λ > 1, η ≥ 0.
The cumulative Theorem 2 already gives ∫_1^{κx} ≤ 2.2258 (κx)² δ log²(2.0001/δ), so on every window
(3.6) is at least 0.9991 times what Theorem 2 gives for the whole of [1, κx]: the paper's local
form carries no local saving, and cannot move the 9.77 floor. The second, positive part of 𝒞
only makes it larger. The source of the loss is the step |κ^{1+ρ₁+ρ̄₂} − λ^{-(1+ρ₁+ρ̄₂)}| ≤ κ² + λ⁻²,
which drops the phase of the off-diagonal zero pairs; recovering it is pair correlation, R-5001.

Plain math twin: for κ > 1, λ > 1, η ≥ 0,
  (1+η) · 2.0282/(√6 π) · (κ² + λ⁻²) · (λ³+1)/(λ−1) ≥ 2.224 κ².
Vacuity: κ = 2, λ = 2, η = 0 satisfy the hypotheses, `localC_ge_two`.
KNOWN mathematics, elementary; no claim of novelty. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.ChirreHagen2025.LocalBarrier
open Real

/-- The main part of Chirre-Hagen's 𝒞(κ, λ, η), display (3.6), without the 10⁻¹⁷ term. -/
noncomputable def mainC (κ l η : ℝ) : ℝ :=
  (1 + η) * (2.0282 / (Real.sqrt 6 * π)) * (κ ^ 2 + 1 / l ^ 2) * ((l ^ 3 + 1) / (l - 1))

/-- `(λ³ + 1)/(λ − 1) ≥ 8.44` for `λ > 1`; the true minimum is about 8.4435 at λ ≈ 1.6777. -/
theorem f_ge (l : ℝ) (hl : 1 < l) : (8.44 : ℝ) ≤ (l ^ 3 + 1) / (l - 1) := by
  have hpos : 0 < l - 1 := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [sq_nonneg (l - 1.6773), sq_nonneg (l - 1), mul_pos hpos hpos,
    mul_nonneg (sq_nonneg (l - 1.6773)) hpos.le]

/-- `2.0282/(√6 π) ≥ 0.26356`. -/
theorem k_ge : (0.26356 : ℝ) ≤ 2.0282 / (Real.sqrt 6 * π) := by
  have hs : Real.sqrt 6 ≤ 2.44949 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have hp : π < 3.1416 := Real.pi_lt_d4
  have hp0 : 0 < π := Real.pi_pos
  have hd : 0 < Real.sqrt 6 * π := by
    have : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  rw [le_div_iff₀ hd]
  nlinarith [mul_le_mul hs hp.le hp0.le (by norm_num : (0:ℝ) ≤ 2.44949)]

/-- The local constant of (3.6) is never below `2.224 κ²`. -/
theorem localC_ge (κ l η : ℝ) (hκ : 1 < κ) (hl : 1 < l) (hη : 0 ≤ η) :
    2.224 * κ ^ 2 ≤ mainC κ l η := by
  unfold mainC
  have hf := f_ge l hl
  have hk := k_ge
  have hl2 : 0 ≤ 1 / l ^ 2 := by positivity
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  have h1 : κ ^ 2 ≤ κ ^ 2 + 1 / l ^ 2 := by linarith
  have hkf : (0.26356 : ℝ) * 8.44 ≤ 2.0282 / (Real.sqrt 6 * π) * ((l ^ 3 + 1) / (l - 1)) :=
    mul_le_mul hk hf (by norm_num) (by linarith)
  have hA : 0 ≤ 2.0282 / (Real.sqrt 6 * π) * ((l ^ 3 + 1) / (l - 1)) := by linarith
  calc 2.224 * κ ^ 2 ≤ ((0.26356 : ℝ) * 8.44) * κ ^ 2 := by nlinarith
    _ ≤ (2.0282 / (Real.sqrt 6 * π) * ((l ^ 3 + 1) / (l - 1))) * (κ ^ 2 + 1 / l ^ 2) :=
        mul_le_mul hkf h1 hκ2 hA
    _ ≤ (1 + η) * ((2.0282 / (Real.sqrt 6 * π) * ((l ^ 3 + 1) / (l - 1))) *
          (κ ^ 2 + 1 / l ^ 2)) := by
        have : 0 ≤ (2.0282 / (Real.sqrt 6 * π) * ((l ^ 3 + 1) / (l - 1))) *
            (κ ^ 2 + 1 / l ^ 2) := by positivity
        nlinarith
    _ = (1 + η) * (2.0282 / (Real.sqrt 6 * π)) * (κ ^ 2 + 1 / l ^ 2) *
          ((l ^ 3 + 1) / (l - 1)) := by ring

/-- Against the cumulative Theorem 2 constant 2.2258 on `[1, κ x]`: the local bound of (3.6)
is at least 0.9991 times it, for every window. -/
theorem local_vs_cumulative (κ l η : ℝ) (hκ : 1 < κ) (hl : 1 < l) (hη : 0 ≤ η) :
    0.9991 * (2.2258 * κ ^ 2) ≤ mainC κ l η := by
  have := localC_ge κ l η hκ hl hη
  nlinarith [sq_nonneg κ]

/-- Vacuity: the hypotheses hold at κ = λ = 2, η = 0. -/
theorem localC_ge_two : 2.224 * (2 : ℝ) ^ 2 ≤ mainC 2 2 0 :=
  localC_ge 2 2 0 (by norm_num) (by norm_num) le_rfl

end LeanLab.ChirreHagen2025.LocalBarrier

#print axioms LeanLab.ChirreHagen2025.LocalBarrier.f_ge
#print axioms LeanLab.ChirreHagen2025.LocalBarrier.k_ge
#print axioms LeanLab.ChirreHagen2025.LocalBarrier.localC_ge
#print axioms LeanLab.ChirreHagen2025.LocalBarrier.local_vs_cumulative
#print axioms LeanLab.ChirreHagen2025.LocalBarrier.localC_ge_two
