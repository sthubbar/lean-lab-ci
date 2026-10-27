/-
P0069 Baker, Harman, Pintz 1997, Lemmas 11 and 12, pages 24 to 27, read from the page images
papers/P0069-original.pdf. Unit U-5080, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log x`. `T₁ = x^{0.45 - 2ε/3}`, `Y = x^{θ₁}`, `θ₁ = 0.55 + ε`, `γ = x^{ε/12}`.
PROVED: `eq45_exponent`, the error `x^{1+ε/4}/(T₁ y)` of (4.3) is `x^{0.55 + 11ε/12}/y`, as (4.5)
prints, and at `y = Y` it saves `x^{ε/12}`; `eq44_T0`, `T₀² y² x^{-1} = y exp(-ℒ^{1/3})` at
`y = y₁ = x exp(-3ℒ^{1/3})`; `lemma12_338`, (4.8) with `D ≤ γ` gives (3.38) for `M₁ = MD`.
FINDING, cosmetic, `lemma12_339_gap`: (4.9) as printed allows `max(M, N) = x^{0.46+ε/8}`, and then
`M₁ = MD` with `D` up to `γ = x^{ε/12}` has length up to `x^{0.46 + 5ε/24}`, beyond (3.39)'s
`x^{0.46 + ε/8}`, so "(3.38) or (3.39) holds" does not follow as printed. Harmless:
`lemma12_339_ok`, the later uses, (4.18), have `M ≤ x^{0.46}`, and then (3.39) holds; and
`lemma10_binding_ok`, the term of Lemma 4 that fixes 0.46 still closes in Lemma 10's setting for
`M₁ ≤ x^{0.46 + 5ε/24}`, with margin `71ε/288`.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma1112

/-- (4.3) to (4.5): `1 + ε/4 - (0.45 - 2ε/3) = 0.55 + 11ε/12`, and at `y = Y = x^{0.55+ε}` the
error is `x^{-ε/12}`. -/
theorem eq45_exponent (ε : ℝ) :
    1 + ε / 4 - (0.45 - 2 * ε / 3) = 0.55 + 11 * ε / 12 ∧
      0.55 + 11 * ε / 12 - (0.55 + ε) = -(ε / 12) := by
  constructor <;> ring

/-- (4.4) at `y = y₁`: `T₀² y₁ / x = exp(2ℒ^{1/3}) exp(-3ℒ^{1/3}) = exp(-ℒ^{1/3})`. -/
theorem eq44_T0 (L : ℝ) : Real.exp (2 * L) * Real.exp (-(3 * L)) = Real.exp (-L) := by
  rw [← Real.exp_add]; congr 1; ring

/-- (4.8) and `D ≤ γ = x^{ε/12}` give (3.38) for `M₁ = MD`. -/
theorem lemma12_338 {ε m n d : ℝ} (hε : 0 < ε) (hd : d ≤ ε / 12) (hd0 : 0 ≤ d)
    (h48 : max 0.45 m + max 0.225 n ≤ 0.775) :
    max 0.45 (m + d) + max 0.225 n ≤ 0.775 + ε / 8 := by
  have : max 0.45 (m + d) ≤ max 0.45 m + d :=
    max_le (by linarith [le_max_left (0.45 : ℝ) m]) (by linarith [le_max_right (0.45 : ℝ) m])
  linarith

/-- FINDING: under (4.9) as printed, `M = x^{0.46+ε/8}` and `D = x^{ε/12}` give
`M₁ = x^{0.46 + 5ε/24}`, which (3.39) does not allow. -/
theorem lemma12_339_gap {ε : ℝ} (hε : 0 < ε) :
    (0.46 + ε / 8) + ε / 12 = 0.46 + 5 * ε / 24 ∧ ¬ ((0.46 + ε / 8) + ε / 12 ≤ 0.46 + ε / 8) := by
  constructor
  · ring
  · intro h; linarith

/-- With `M ≤ x^{0.46}`, the form used in (4.18), `M₁ ≤ x^{0.46 + ε/12}` satisfies the `M` side of
(3.39); the `N` side, `N ≤ x^{0.46}`, comes from (4.18) directly and is not restated here. -/
theorem lemma12_339_ok {ε m d : ℝ} (hε : 0 < ε) (hm : m ≤ 0.46) (hd : d ≤ ε / 12) :
    m + d ≤ 0.46 + ε / 8 := by linarith

/-- The term of Lemma 4 that fixes the 0.46, `(qT)^{1/2} X^{1/12} M^{5/12}`, in Lemma 10's setting
`qT ≤ x^{0.45 - 2ε/3}` with `M₁ ≤ x^{0.46 + 5ε/24}`: still below `x^{1/2}` by `x^{71ε/288}`. -/
theorem lemma10_binding_ok {ε k m : ℝ} (hk : k ≤ 0.45 - 2 * ε / 3) (hm : m ≤ 0.46 + 5 * ε / 24) :
    k / 2 + 1 / 12 + 5 / 12 * m ≤ 1 / 2 - 71 * ε / 288 := by linarith

end LeanLab.BHP1997.Lemma1112
