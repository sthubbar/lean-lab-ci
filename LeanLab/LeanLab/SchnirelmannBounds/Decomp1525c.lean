/-
Unit U-1525, run 20261025T2003Z-426, DECOMPOSE. P0066 R. C. Vaughan 1977, J. reine angew.
Math. 290, 93-108, read from copies/P0066.pdf, page image 103.

File c of three: the first moment. In Vaughan's form of Schnirelmann's route the first moment
Σ r(n) ≫ N²/log² N is Lemma 11, Ψ(x) = x²/log x (1 + (3 - 4 log 2)/(2 log x)) + O(0.3x²/log² x).
The folder reduces Lemma 11 to `DistributionError` and the PROVED `QuadratureError`
(Vaughan1977Lemma11Inputs.lean), and proves the first step on p. 103,
|Ψ(x) - Σ_{p ≤ x-3} log p ∫_{x-p}^{2x-p} du/log u| < x²/(12 log² x), CONDITIONAL ON (2.15),
(2.16), as `prime_interval_approximation_integral`. `DistributionError` is OPEN; it is split here.

The split, p. 103: reverse sum and integral, Σ_p log p ∫_{x-p}^{2x-p} = ∫_3^{2x} I(u) du/log u
with I(u) = Σ_{x-u < p ≤ min(x-3, 2x-u)} log p a difference of θ values; then compare I(u)
with u on [3, x] and with 2x - u on [x, 2x] by (2.15), the arguments below 678407 handled by
a constant. Budgets 1/12 + 1/20 + 1/20 < 1/5.

PROVED here: `distribution_of`, the bound of `DistributionError`, CONDITIONAL ON the p. 103
first step (the folder's `prime_interval_approximation_integral` conclusion) and (2.15), from
the leaves. Local copies `P1V`, `PsiV`, `mainIntegralV` have the same text as `P1`, `Psi`,
`mainIntegral` of the folder, so that only Mathlib is imported.

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN.
-/
import Mathlib

open Finset Real MeasureTheory intervalIntegral
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Decomp1525c

/-- `P1 x`: primes `3 ≤ p ≤ x - 3`, as `Vaughan1977Eq55.P1`. -/
def P1V (x : ℝ) : Finset ℕ := (Icc 3 ⌊x - 3⌋₊).filter Nat.Prime

/-- `Ψ(x)` of (5.1), as `Vaughan1977Lemma12.Psi`. -/
def PsiV (x : ℝ) : ℝ :=
  ∑ p₁ ∈ (Icc 3 ⌊x - 3⌋₊).filter Nat.Prime,
    ∑ _p₂ ∈ (Icc 1 ⌊2 * x - p₁⌋₊).filter (fun p : ℕ => p.Prime ∧ x - p₁ < (p : ℝ)), Real.log p₁

/-- The main integrals of p. 103, as `Vaughan1977Lemma11Inputs.mainIntegral`. -/
def mainIntegralV (x : ℝ) : ℝ :=
  (∫ u in (3 : ℝ)..x, u / Real.log u) + ∫ u in x..(2 * x), (2 * x - u) / Real.log u

/-- `I(u) = Σ_{p ∈ P1 x, x - p < u ≤ 2x - p} log p`, the inner sum after reversing p. 103. -/
def thetaI (x u : ℝ) : ℝ :=
  ∑ p ∈ (P1V x).filter (fun p : ℕ => x - p < u ∧ u ≤ 2 * x - p), Real.log p

/-! ### Leaves -/

/-- LEAF. Reversing sum and integral: for `x ≥ 6`,
`Σ_{p ∈ P1 x} log p ∫_{x-p}^{2x-p} du/log u = ∫_3^{2x} I(u) du/log u`; each interval
`[x-p, 2x-p]` lies in `[3, 2x-3]`. Vaughan 1977 p. 103, "Hence, by Lemma 2", the reversed
display. Unit U-1525. -/
theorem swap (x : ℝ) (hx : 6 ≤ x) :
    ∑ p ∈ P1V x, Real.log p * ∫ u in (x - p)..(2 * x - p), 1 / Real.log u =
      ∫ u in (3 : ℝ)..(2 * x), thetaI x u / Real.log u := by
  sorry

/-- LEAF. `I(u)` on `[3, x]`: `I(u) = θ(x - 3) - θ(max(x - u, 2))`, the primes in
`(max(x-u, 2), x-3]`. Vaughan 1977 p. 103, the integral over `[3, x]` in the third display.
Unit U-1525. -/
theorem thetaI_low (x u : ℝ) (hx : 6 ≤ x) (hu3 : 3 ≤ u) (hux : u ≤ x) :
    thetaI x u = Chebyshev.theta (x - 3) - Chebyshev.theta (max (x - u) 2) := by
  sorry

/-- LEAF. `I(u)` on `[x, 2x]`: `I(u) = max(θ(min(x-3, 2x-u)) - log 2, 0)`, the odd primes up to
`min(x-3, 2x-u)`. Vaughan 1977 p. 103, the integrals over `[x, 2x]` and `[x, x+3]`.
Unit U-1525. -/
theorem thetaI_high (x u : ℝ) (hx : 6 ≤ x) (hxu : x ≤ u) (hu : u ≤ 2 * x) :
    thetaI x u = max (Chebyshev.theta (min (x - 3) (2 * x - u)) - Real.log 2) 0 := by
  sorry

/-- LEAF. Pointwise bound on `[3, x]` from (2.15): with `t = max(x-u, 2)`,
`|I(u) - u| ≤ x/(40 log x) + t/(40 log t) + 678412`; below 678407 use `|θ(t) - t| ≤ t` from
`0 ≤ θ(t) ≤ log 4 · t` (Mathlib `Chebyshev.theta_le_log4_mul_x`). Vaughan 1977 p. 103,
`|θ(x-3) - θ(x-u) - u|` in the third display. Unit U-1525. -/
theorem low_pointwise
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x u : ℝ) (hx : 10 ^ 52 ≤ x) (hu3 : 3 ≤ u) (hux : u ≤ x) :
    |thetaI x u - u| ≤ x / (40 * Real.log x)
      + max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412 := by
  sorry

/-- LEAF. The low majorant integral: for `x ≥ 10^52`,
`∫_3^x (x/(40 log x) + t/(40 log t) + 678412) du/log u ≤ x²/(20 log² x)`, `t = max(x-u, 2)`;
numerically the left side is about `0.038 x²/log² x`. Vaughan 1977 p. 103, third display.
Unit U-1525. -/
theorem low_majorant (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    ∫ u in (3 : ℝ)..x, (x / (40 * Real.log x)
      + max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412) / Real.log u
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by
  sorry

/-- LEAF. Pointwise bound on `[x, 2x]` from (2.15): with `s = max(min(x-3, 2x-u), 2)`,
`|I(u) - (2x - u)| ≤ s/(40 log s) + 678412`. Vaughan 1977 p. 103, `|θ(2x-u) - 2x + u|` and the
`[x, x+3]` term of the third display. Unit U-1525. -/
theorem high_pointwise
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x u : ℝ) (hx : 10 ^ 52 ≤ x) (hxu : x ≤ u) (hu : u ≤ 2 * x) :
    |thetaI x u - (2 * x - u)| ≤
      max (min (x - 3) (2 * x - u)) 2 / (40 * Real.log (max (min (x - 3) (2 * x - u)) 2))
        + 678412 := by
  sorry

/-- LEAF. The high majorant integral: for `x ≥ 10^52`,
`∫_x^{2x} (s/(40 log s) + 678412) du/log u ≤ x²/(20 log² x)`, `s = max(min(x-3, 2x-u), 2)`;
numerically about `0.0125 x²/log² x`. Vaughan 1977 p. 103, third display. Unit U-1525. -/
theorem high_majorant (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    ∫ u in x..(2 * x), (max (min (x - 3) (2 * x - u)) 2 /
        (40 * Real.log (max (min (x - 3) (2 * x - u)) 2)) + 678412) / Real.log u
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by
  sorry

/-- LEAF. Integrability: `I(u)/log u` is a step function over `1/log u`, integrable on `[3, x]`
and on `[x, 2x]` for `x ≥ 6`. Unit U-1525. -/
theorem thetaI_integrable (x : ℝ) (hx : 6 ≤ x) :
    IntervalIntegrable (fun u => thetaI x u / Real.log u) volume 3 x ∧
    IntervalIntegrable (fun u => thetaI x u / Real.log u) volume x (2 * x) := by
  sorry

/-- LEAF. The low comparison: `|∫_3^x I(u)/log u - ∫_3^x u/log u| ≤ x²/(20 log² x)`, from
`low_pointwise`, `low_majorant` and `thetaI_integrable` by `norm_integral_le_of_norm_le`.
Vaughan 1977 p. 103. Unit U-1525. -/
theorem low_compare
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    |(∫ u in (3 : ℝ)..x, thetaI x u / Real.log u) - ∫ u in (3 : ℝ)..x, u / Real.log u|
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by
  sorry

/-- LEAF. The high comparison:
`|∫_x^{2x} I(u)/log u - ∫_x^{2x} (2x-u)/log u| ≤ x²/(20 log² x)`, from `high_pointwise`,
`high_majorant` and `thetaI_integrable`. Vaughan 1977 p. 103. Unit U-1525. -/
theorem high_compare
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    |(∫ u in x..(2 * x), thetaI x u / Real.log u) - ∫ u in x..(2 * x), (2 * x - u) / Real.log u|
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by
  sorry

/-! ### Assembly -/

/-- **`DistributionError`, PROVED from the leaves, CONDITIONAL ON the p. 103 first step
`hPI` (the folder's `prime_interval_approximation_integral`, itself CONDITIONAL ON (2.15) and
(2.16)) and on (2.15)**: for `x ≥ 10^52`, `|Ψ(x) - mainIntegral(x)| < x²/(5 log² x)`.
Vaughan 1977 p. 103. -/
theorem distribution_of
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (hPI : ∀ x : ℝ, 10 ^ 52 ≤ x →
      |PsiV x - ∑ p ∈ P1V x, Real.log p * ∫ u in (x - p)..(2 * x - p), 1 / Real.log u|
        < x ^ 2 / (12 * Real.log x ^ 2)) :
    ∀ x : ℝ, 10 ^ 52 ≤ x → |PsiV x - mainIntegralV x| < x ^ 2 / (5 * Real.log x ^ 2) := by
  intro x hx
  have hx6 : 6 ≤ x := by linarith
  have h1 := hPI x hx
  rw [swap x hx6] at h1
  obtain ⟨hi1, hi2⟩ := thetaI_integrable x hx6
  rw [← integral_add_adjacent_intervals hi1 hi2] at h1
  have h2 := low_compare h215 x hx
  have h3 := high_compare h215 x hx
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hL2 : 0 < Real.log x ^ 2 := by positivity
  have hX : 0 < x ^ 2 / Real.log x ^ 2 := by positivity
  have e12 : x ^ 2 / (12 * Real.log x ^ 2) = (x ^ 2 / Real.log x ^ 2) / 12 := by
    field_simp
  have e20 : x ^ 2 / (20 * Real.log x ^ 2) = (x ^ 2 / Real.log x ^ 2) / 20 := by
    field_simp
  have e5 : x ^ 2 / (5 * Real.log x ^ 2) = (x ^ 2 / Real.log x ^ 2) / 5 := by
    field_simp
  rw [e12] at h1; rw [e20] at h2 h3; rw [e5]
  unfold mainIntegralV
  set A := ∫ u in (3 : ℝ)..x, thetaI x u / Real.log u
  set B := ∫ u in x..(2 * x), thetaI x u / Real.log u
  set A' := ∫ u in (3 : ℝ)..x, u / Real.log u
  set B' := ∫ u in x..(2 * x), (2 * x - u) / Real.log u
  have : |PsiV x - (A' + B')| ≤ |PsiV x - (A + B)| + |A - A'| + |B - B'| := by
    have e : PsiV x - (A' + B') = (PsiV x - (A + B)) + (A - A') + (B - B') := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by gcongr; exact abs_add_le _ _)
  linarith

/-! ### Vacuity -/

/-- Vacuity for `distribution_of`'s range and the leaves' ranges: `x = 10^52` satisfies
`10^52 ≤ x`, `6 ≤ x`, and `u = 3` lies in `[3, x]`. -/
example : (10 : ℝ) ^ 52 ≤ 10 ^ 52 ∧ (6 : ℝ) ≤ 10 ^ 52 ∧ (3 : ℝ) ≤ 3 ∧ (3 : ℝ) ≤ 10 ^ 52 :=
  ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩

end LeanLab.SchnirelmannBounds.Decomp1525c
