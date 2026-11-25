import LeanLab.ExceptionalSet.RealZeroLower672

/-!
Feed 1122, the LEAF `leaf_exceptional_zero_page_bound` of
`Feed1122_near_zero_even_large_prime_long.lean`, P0082 page 358 display 10, citing Davenport
chapter 14, in the weaker form `1 - β ≫ r^(-3/5)` used there.

The lab proves the ineffective zero gap `c r^(-1/2) ≤ 1 - β` as `realZeroGapHalf672` in
`RealZeroLower672.lean`, from the clean lab Siegel theorem
`LeanLab.PNTPort.DirichletZF.siegel_zero` at `ε = 1/2`.  Since `r ≥ 1`, `r^(-3/5) ≤ r^(-1/2)`,
so the same constant works.  No existence of an exceptional zero is asserted.

This file does not import the leaf file, so the leaf file may import it.
AI wrote the Lean code, CLOUD S134.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real

/-- Verbatim statement of `leaf_exceptional_zero_page_bound`, P0082 page 358 display 10 in the
weaker form `1 - β ≫ r^(-3/5)`, proved from the lab zero gap `realZeroGapHalf672`. -/
theorem leaf_exceptional_zero_page_bound_s134 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β → β < 1 → χ.LFunction β = 0 →
        c₀ * (r : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 1 - β := by
  obtain ⟨c, hc, hgap⟩ := LeanLab.ExceptionalSet.Task672.realZeroGapHalf672
  refine ⟨c, hc, ?_⟩
  intro r hr χ β _ hreal hχ _ hβ1 hz
  have hb := hgap r hr χ hχ hreal β hβ1.le hz
  have hr1 : (1 : ℝ) ≤ r := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  have hpow : (r : ℝ) ^ (-(3 / 5 : ℝ)) ≤ (r : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
  calc c * (r : ℝ) ^ (-(3 / 5 : ℝ)) ≤ c * (r : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hc.le
    _ ≤ 1 - β := hb

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
