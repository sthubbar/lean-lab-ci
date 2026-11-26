import LeanLab.HelfgottMajor.SPLIT_leaf_moment_low_mass_lower_half
import LeanLab.HelfgottMajor.SPLIT_leaf_moment_low_mass_upper_half

/-!
Units S2-16, S2-17, S2-20 and S2-21 of burst-20261124, agent S2G6.

The four open leaves `leaf_low_mass_lower_half_far_low`, `leaf_low_mass_lower_half_far_high`
of `SPLIT_leaf_moment_low_mass_lower_half.lean` and `leaf_upper_half_low_height_le`,
`leaf_upper_half_high_height_le` of `SPLIT_leaf_moment_low_mass_upper_half.lean` each bound the
weighted squared Gaussian Mellin mass of the zeros of `L χ` in one box off the critical line.

This file proves, with no `sorry`, the direction that a zero free box gives the leaf: if
`L χ` has no zero in the box, the sum is empty and the bound holds for every `δ`, because
`Sec45.nTwo = √π / 2` is nonnegative.  The other direction is numerical and is in the note
`notes/burst-20261124/HelfgottMajor-S2-16-17-20-21-grh-box-blocked.md`: at `δ = 0` the squared
norm `‖gaussianMellin 0 ρ‖ ^ 2 = |2 ^ (ρ / 2 - 1) Γ (ρ / 2)| ^ 2` is above the leaf bound at
every point of each box, so each leaf at `δ = 0` already forbids every zero in its box.  So
each leaf is, uniformly in `q` and `χ`, a statement of the Generalized Riemann Hypothesis in a
box of height one, two of them containing a real segment and hence excluding Siegel zeros.
These are open; the units are BLOCKED, not provable from the papers on the route.

The hypotheses below are zero free statements, not cited results of P0014; every theorem
here is CONDITIONAL ON its zero free hypothesis.  No new definition.
-/

namespace LeanLab.HelfgottMajor.S2G6GrhBox
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- The constant `Sec45.nTwo = √π / 2` is nonnegative. -/
private theorem nTwo_nonneg' : 0 ≤ Sec45.nTwo := by
  unfold Sec45.nTwo
  positivity

/-- A sum of an indicator over a set with no member is zero. -/
private theorem tsum_indicator_empty {α : Type*} (s : Set α) (f : α → ℝ)
    (h : ∀ x, x ∈ s → False) : ∑' x, s.indicator f x = 0 := by
  have hf : s.indicator f = 0 := by
    funext x
    exact Set.indicator_of_notMem (fun hx => h x hx) f
  rw [hf]
  simp

/-- Far low box `0 < re ρ ≤ 1/4`, `|im ρ| ≤ 1/2`: if `L χ` has no zero there, the leaf
`leaf_low_mass_lower_half_far_low` holds for this `q`, `χ`, every `δ` and `T`. -/
theorem far_low_of_zero_free (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (h : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ 1 → ρ.re ≤ 1 / 4 → |ρ.im| ≤ 1 / 2 → False) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator ({ρ | ρ.val.re ≤ 1 / 4} ∩ {ρ | |ρ.val.im| ≤ 1 / 2})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 8 := by
  rw [tsum_indicator_empty]
  · linarith [nTwo_nonneg']
  · rintro ⟨ρ, h0, h1, h2, h3⟩ ⟨ha, hb⟩
    exact h ρ h0 h1 h2 h3 ha hb

/-- Far high box `0 < re ρ ≤ 1/4`, `1/2 < |im ρ| ≤ 1`: if `L χ` has no zero there, the leaf
`leaf_low_mass_lower_half_far_high` holds for this `q`, `χ`, every `δ` and `T`. -/
theorem far_high_of_zero_free (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (h : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ 1 → ρ.re ≤ 1 / 4 → 1 / 2 < |ρ.im| → False) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator ({ρ | ρ.val.re ≤ 1 / 4} ∩ {ρ | 1 / 2 < |ρ.val.im|})
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 8 := by
  rw [tsum_indicator_empty]
  · linarith [nTwo_nonneg']
  · rintro ⟨ρ, h0, h1, h2, h3⟩ ⟨ha, hb⟩
    exact h ρ h0 h1 h2 h3 ha hb

/-- Upper low box `1/2 < re ρ < 1`, `|im ρ| ≤ 1/2`: if `L χ` has no zero there, the leaf
`leaf_upper_half_low_height_le` holds for this `q`, `χ`, every `δ` and `T`. -/
theorem upper_low_of_zero_free (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (h : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ 1 → 1 / 2 < ρ.re → |ρ.im| ≤ 1 / 2 → False) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re ∧ |ρ.val.im| ≤ 1 / 2}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 4 := by
  rw [tsum_indicator_empty]
  · linarith [nTwo_nonneg']
  · rintro ⟨ρ, h0, h1, h2, h3⟩ ⟨ha, hb⟩
    exact h ρ h0 h1 h2 h3 ha hb

/-- Upper high box `1/2 < re ρ < 1`, `1/2 < |im ρ| ≤ 1`: if `L χ` has no zero there, the
leaf `leaf_upper_half_high_height_le` holds for this `q`, `χ`, every `δ` and `T`. -/
theorem upper_high_of_zero_free (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (h : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ 1 → 1 / 2 < ρ.re → 1 / 2 < |ρ.im| → False) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      Set.indicator {ρ | 1 / 2 < ρ.val.re ∧ 1 / 2 < |ρ.val.im|}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo / 4 := by
  rw [tsum_indicator_empty]
  · linarith [nTwo_nonneg']
  · rintro ⟨ρ, h0, h1, h2, h3⟩ ⟨ha, hb⟩
    exact h ρ h0 h1 h2 h3 ha hb

end LeanLab.HelfgottMajor.S2G6GrhBox

#print axioms LeanLab.HelfgottMajor.S2G6GrhBox.far_low_of_zero_free
#print axioms LeanLab.HelfgottMajor.S2G6GrhBox.far_high_of_zero_free
#print axioms LeanLab.HelfgottMajor.S2G6GrhBox.upper_low_of_zero_free
#print axioms LeanLab.HelfgottMajor.S2G6GrhBox.upper_high_of_zero_free
