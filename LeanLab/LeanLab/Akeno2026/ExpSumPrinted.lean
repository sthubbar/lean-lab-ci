/-
P0087 Akeno 2026 Theorem 2.1 equation 2 on page 4.
The printed first term is D/q. The existing ExpSumBound uses D squared over q.
This file preserves the existing statement and gives the exact printed form and a bridge.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026
open Real
open scoped ContDiff

/-- The exact printed Theorem 2.1 estimate. This is a cited input, not a proved theorem. -/
def ExpSumBoundPrinted : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → Function.support w ⊆ Set.Icc 0 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X D α : ℝ, 1 ≤ X → 0 < D → D ≤ X → 0 ≤ α → α ≤ 1 →
      ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 → |α - a / q| ≤ 1 / (q : ℝ) ^ 2 →
        expSumLHS w X D α ≤
          C * X ^ (2 + ε) * (D / q + q * D / X + D ^ 2 * X ^ (-(1 : ℝ) / 3))

/-- The dyadic residue sum is empty when 2 D is below 1. -/
theorem expSumLHS_eq_zero_of_small_D (w : ℝ → ℝ) (X D α : ℝ) (hD : 2 * D < 1) :
    expSumLHS w X D α = 0 := by
  have hf : ⌊2 * D⌋₊ = 0 := Nat.floor_eq_zero.mpr hD
  unfold expSumLHS
  rw [hf]
  simp

/-- Above the first possible modulus, the printed budget is at most twice the old budget. -/
theorem printed_budget_le_twice_old {X D : ℝ} {q : ℕ}
    (hX : 0 < X) (hD : 1 / 2 ≤ D) (hq : 1 ≤ q) :
    D / q + q * D / X + D ^ 2 * X ^ (-(1 : ℝ) / 3) ≤
      2 * (D ^ 2 / q + q * D / X + D ^ 2 * X ^ (-(1 : ℝ) / 3)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hD0 : 0 ≤ D := by linarith
  have h1 := div_le_div_of_nonneg_right (show D ≤ 2 * D ^ 2 by nlinarith) hq0
  rw [mul_div_assoc] at h1
  have h2 : 0 ≤ (q : ℝ) * D / X := by positivity
  have h3 : 0 ≤ D ^ 2 * X ^ (-(1 : ℝ) / 3) := by positivity
  linarith

/-- The exact printed estimate implies the existing estimate with twice its constant.
CONDITIONAL ON the cited printed estimate. -/
theorem expSumBound_of_printed (h : ExpSumBoundPrinted) : ExpSumBound := by
  intro ε hε w hw hs
  obtain ⟨C, hC, hbound⟩ := h ε hε w hw hs
  refine ⟨2 * C, ?_⟩
  intro X D α hX hD hDX hα0 hα1 a q hq hcop happrox
  have hX0 : 0 < X := by linarith
  have hp0 : 0 ≤ X ^ (2 + ε) := Real.rpow_nonneg hX0.le _
  have hb0 : 0 ≤ D ^ 2 / (q : ℝ) + (q : ℝ) * D / X + D ^ 2 * X ^ (-(1 : ℝ) / 3) := by
    positivity
  by_cases hsmall : 2 * D < 1
  · rw [expSumLHS_eq_zero_of_small_D w X D α hsmall]
    exact mul_nonneg (mul_nonneg (by linarith) hp0) hb0
  · have hb := printed_budget_le_twice_old (D := D) hX0 (by linarith) hq
    have hmul := mul_le_mul_of_nonneg_left hb (mul_nonneg hC hp0)
    have hbase := hbound X D α hX hD hDX hα0 hα1 a q hq hcop happrox
    apply hbase.trans
    convert hmul using 1; ring

end LeanLab.Akeno2026
