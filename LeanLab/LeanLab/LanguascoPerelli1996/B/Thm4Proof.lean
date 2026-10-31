/-
P0071 Languasco and Perelli 1996, Section 4, the assembly of the proof of Theorem 4, pages 358 and
359, read from the page images of papers/P0071.pdf. Unit U-5071, CLOUD 20261019T0213Z-cloud14.

PROVED, as real inequalities with every `≪` an explicit constant:
`eq24_of_eq23`, (23) with `I_j ≤ A X^{1+ε} q²/ξ` gives (24), `∫_{-ξ}^{ξ} |R|² ≤ (3A + 1) ξ X^{1+2ε}`
for `ξ ≤ 1`, `X ≥ 1`; and `theorem4_of`, (20) with (22) and (24) gives
`|R(η)| ≤ √(2B) X^{(1+ε)/2} (1 + (ξX)^{1/2})`, which is Theorem 4 with ε halved.
MATCH. Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.LanguascoPerelli1996.B.Thm4Proof
open Real

/-- (23) to (24): `ξ²X^ε/q² · (I₁ + I₂ + I₃) + ξX^{1+ε}` with `I_j ≤ A X^{1+ε} q²/ξ` is at most
`(3A + 1) ξ X^{1+2ε}`, for `X ≥ 1`, `ε ≥ 0`. -/
theorem eq24_of_eq23 {X ξ q A ε I₁ I₂ I₃ : ℝ} (hX : 1 ≤ X) (hε : 0 ≤ ε) (hξ : 0 < ξ)
    (hq : 0 < q) (hA : 0 ≤ A)
    (h1 : I₁ ≤ A * X ^ (1 + ε) * q ^ 2 / ξ) (h2 : I₂ ≤ A * X ^ (1 + ε) * q ^ 2 / ξ)
    (h3 : I₃ ≤ A * X ^ (1 + ε) * q ^ 2 / ξ) :
    ξ ^ 2 * X ^ ε / q ^ 2 * (I₁ + I₂ + I₃) + ξ * X ^ (1 + ε) ≤ (3 * A + 1) * ξ * X ^ (1 + 2 * ε) := by
  have hX0 : 0 < X := by linarith
  have hXe : 0 < X ^ ε := rpow_pos_of_pos hX0 ε
  have hc : 0 ≤ ξ ^ 2 * X ^ ε / q ^ 2 := by positivity
  have hsum : I₁ + I₂ + I₃ ≤ 3 * (A * X ^ (1 + ε) * q ^ 2 / ξ) := by linarith
  have e : ξ ^ 2 * X ^ ε / q ^ 2 * (3 * (A * X ^ (1 + ε) * q ^ 2 / ξ)) =
      3 * A * ξ * X ^ (1 + 2 * ε) := by
    rw [show (1 + 2 * ε) = (1 + ε) + ε by ring, rpow_add hX0 (1 + ε) ε]
    field_simp
  have hmono : X ^ (1 + ε) ≤ X ^ (1 + 2 * ε) := rpow_le_rpow_of_exponent_le hX (by linarith)
  have := mul_le_mul_of_nonneg_left hsum hc
  rw [e] at this
  nlinarith [mul_le_mul_of_nonneg_left hmono hξ.le]

/-- (20) with (22) and (24): if `|R(η)|² ≤ ξ⁻¹ J + (J J')^{1/2}`, `J' ≤ X² J` and `J ≤ B ξ X^{1+ε}`,
then `|R(η)| ≤ √(2B) X^{(1+ε)/2} (1 + (ξX)^{1/2})`. -/
theorem theorem4_of {r J J' X ξ B ε : ℝ} (hX : 0 < X) (hξ : 0 < ξ) (hB : 0 ≤ B) (hJ0 : 0 ≤ J)
    (hr : 0 ≤ r) (h20 : r ^ 2 ≤ J / ξ + Real.sqrt (J * J')) (h22 : J' ≤ X ^ 2 * J)
    (h24 : J ≤ B * ξ * X ^ (1 + ε)) :
    r ≤ Real.sqrt (2 * B) * X ^ ((1 + ε) / 2) * (1 + (ξ * X) ^ (1 / 2 : ℝ)) := by
  have hY : 0 < X ^ (1 + ε) := rpow_pos_of_pos hX _
  -- the square root term is at most X J
  have hs : Real.sqrt (J * J') ≤ X * J := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h22 hJ0]
  have hJξ : J / ξ ≤ B * X ^ (1 + ε) := by
    rw [div_le_iff₀ hξ]; linarith
  have hr2 : r ^ 2 ≤ B * X ^ (1 + ε) * (1 + ξ * X) := by
    nlinarith [mul_le_mul_of_nonneg_left h24 hX.le]
  -- now take square roots
  set u := (ξ * X) ^ (1 / 2 : ℝ) with hu
  have hu0 : 0 ≤ u := rpow_nonneg (by positivity) _
  have hu2 : u ^ 2 = ξ * X := by
    rw [hu, ← rpow_natCast, ← rpow_mul (by positivity)]; norm_num
  set w := X ^ ((1 + ε) / 2) with hw
  have hw0 : 0 < w := rpow_pos_of_pos hX _
  have hw2 : w ^ 2 = X ^ (1 + ε) := by
    rw [hw, ← rpow_natCast, ← rpow_mul hX.le]; norm_num
  have hsB : Real.sqrt (2 * B) ^ 2 = 2 * B := Real.sq_sqrt (by positivity)
  have hsB0 : 0 ≤ Real.sqrt (2 * B) := Real.sqrt_nonneg _
  have key : r ^ 2 ≤ (Real.sqrt (2 * B) * w * (1 + u)) ^ 2 := by
    have : B * X ^ (1 + ε) * (1 + ξ * X) ≤ (Real.sqrt (2 * B) * w * (1 + u)) ^ 2 := by
      rw [mul_pow, mul_pow, hsB, hw2, ← hw2, ← hu2]
      nlinarith [sq_nonneg (1 - u), mul_nonneg hB (sq_nonneg w)]
    linarith
  have hpos : 0 ≤ Real.sqrt (2 * B) * w * (1 + u) := by positivity
  nlinarith [key, hpos]

end LeanLab.LanguascoPerelli1996.B.Thm4Proof

