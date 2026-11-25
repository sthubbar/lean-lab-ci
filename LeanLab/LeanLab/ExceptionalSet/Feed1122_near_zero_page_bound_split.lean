import LeanLab.ExceptionalSet.RealZeroLower672

/-!
Feed 1122, the LEAF `leaf_near_zero_page_bound` of `Feed1122_near_zero_even_index.lean`,
P0082 page 358 display 10, citing Davenport chapter 14.

No split was needed.  The lab already proves the ineffective zero gap
`c r^(-1/2) ≤ 1 - β` as `realZeroGapHalf672` in `RealZeroLower672.lean`, from the clean lab
Siegel theorem `LeanLab.PNTPort.DirichletZF.siegel_zero` at `ε = 1/2`.  That bound is stronger
than display 10, since `log (r + 2) ^ 2 ≥ 1` for every conductor `r ≥ 1`.  The constant is
ineffective, which display 10 as used by P0082 does not need.  No existence of an exceptional
zero is asserted.

This file does not import the leaf file, so the leaf file may import it.
AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real

/-- `log (r + 2) ≥ 1` for every natural `r ≥ 1`, since `r + 2 ≥ 3 > e`. -/
theorem one_le_log_add_two_of_one_le (r : ℕ) (hr : 1 ≤ r) :
    1 ≤ Real.log ((r : ℝ) + 2) := by
  have h3 : (3 : ℝ) ≤ (r : ℝ) + 2 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have he : Real.exp 1 ≤ (r : ℝ) + 2 := le_trans (le_of_lt (lt_trans
    Real.exp_one_lt_d9 (by norm_num))) h3
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact he

/-- Verbatim statement of `leaf_near_zero_page_bound`, P0082 page 358 display 10, proved from
the lab zero gap `realZeroGapHalf672`, which needs no cited input. -/
theorem leaf_near_zero_page_bound_of_leaves :
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β → β < 1 → χ.LFunction β = 0 →
        c / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2) ≤ 1 - β := by
  obtain ⟨c, hc, hgap⟩ := LeanLab.ExceptionalSet.Task672.realZeroGapHalf672
  refine ⟨c, hc, ?_⟩
  intro r hr χ β _ hreal hχ _ hβ1 hz
  have hb := hgap r hr χ hχ hreal β hβ1.le hz
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrpos
  have hL : 1 ≤ Real.log ((r : ℝ) + 2) := one_le_log_add_two_of_one_le r hr1
  have hL2 : 1 ≤ Real.log ((r : ℝ) + 2) ^ 2 := one_le_pow₀ hL
  have hrp : (r : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt r := by
    rw [Real.rpow_neg hrpos.le, one_div (Real.sqrt (r : ℝ)), Real.sqrt_eq_rpow]
  rw [hrp] at hb
  calc c / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2)
      ≤ c / (Real.sqrt r * 1) := by
        apply div_le_div_of_nonneg_left hc.le (by positivity)
        exact mul_le_mul_of_nonneg_left hL2 hs.le
    _ = c * (1 / Real.sqrt r) := by rw [mul_one, mul_one_div]
    _ ≤ 1 - β := hb

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
