import LeanLab.HelfgottMajor.ZeroCount1623

/-!
# Split of `veryLow_level_seventeen_sum_le_one`, burst 20261127 S2

The unit `Feed1122VeryLowRepair2.veryLow_level_seventeen_sum_le_one` bounds by one the sum of
multiplicities of the strip zeros of height in `(0, 1]` for a primitive character modulo `17`
on the band `17 T ≤ 2πe`. Its source is Platt's verification [Pla11], cited in Helfgott,
arXiv 1305.2897v4, Section 4.6 page 56. Platt certifies zeros by the argument principle,
isolates them, and checks simplicity. This file follows those three steps.

* LEAF localization, argument principle: every zero of `L(s, χ)` with `0 < Re s < 1` and
  `0 < Im s ≤ 1` lies within `1/100` of `c₁₇ = 1/2 + 0.39131 i`. Numerically burst S126 found
  winding number `0` on `[10^(-4), 1 - 10^(-4)] × [10^(-6), 1]` for fourteen of the fifteen
  primitive characters and `1` for the character with `χ(3) = exp(-5πi/8)`, whose zero is at
  `1/2 + 0.3913146130… i`.
* LEAF isolation: two zeros of `L(s, χ)` within `1/100` of `c₁₇` are equal.
* LEAF simplicity: a zero of `L(s, χ)` within `1/100` of `c₁₇` has multiplicity at most one.

The twin `veryLow_level_seventeen_sum_le_one_of_leaves` proves exactly the unit's statement from
the three leaves, sorry free. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SPLIT_veryLow_level_seventeen_sum_le_one
open Complex
open LeanLab.HelfgottMajor.ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
argument principle step for conductor `17`: on the box `(0,1) × (0,1]` every zero of `L(s, χ)`,
`χ` primitive modulo `17`, lies in the disk of radius `1/100` about `1/2 + 0.39131 i`.
Numerically fourteen of the fifteen primitive characters have no zero there, winding number
`0`, and
the character with `χ(3) = exp(-5πi/8)` has exactly the zero `1/2 + 0.3913146130… i`.
Class HARD: a certified argument principle computation with interval arithmetic. -/
theorem seventeen_low_zero_localized (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hi0 : 0 < ρ.im) (hi1 : ρ.im ≤ 1) :
    ‖ρ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100 := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
isolation step for conductor `17`: for `χ` primitive modulo `17`, `L(s, χ)` has at most one zero
in the disk of radius `1/100` about `1/2 + 0.39131 i`. Numerically, burst 20261127 S2 with mpmath,
the winding number on the circle of radius `1/100` about that point is `1` for one primitive
character and `0` for all the others.
Class HARD: a certified zero isolation, for example a Rouché or Krawczyk bound. -/
theorem seventeen_low_zero_unique (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ₁ ρ₂ : ℂ) (hL₁ : DirichletCharacter.LFunction χ ρ₁ = 0)
    (hL₂ : DirichletCharacter.LFunction χ ρ₂ = 0)
    (hd₁ : ‖ρ₁ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100)
    (hd₂ : ‖ρ₂ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100) : ρ₁ = ρ₂ := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
simplicity step for conductor `17`: a zero of `L(s, χ)`, `χ` primitive modulo `17`, in the disk
of radius `1/100` about `1/2 + 0.39131 i` is simple, so its multiplicity is at most one.
Numerically `L'(ρ, χ) ≠ 0` at the zero `1/2 + 0.3913146130… i`.
Class MEDIUM: a certified lower bound for the derivative at an enclosed zero. -/
theorem seventeen_low_zero_simple (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0)
    (hd : ‖ρ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100) : mult χ ρ ≤ 1 := by
  sorry

/-- Twin of `Feed1122VeryLowRepair2.veryLow_level_seventeen_sum_le_one`, exactly its statement,
from the three leaves: all the zeros in the sum lie in one small disk, are equal, and are
simple, so the sum has at most one term, of size at most one. -/
theorem veryLow_level_seventeen_sum_le_one_of_leaves (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive)
    (hq : q = 17) {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1),
      (mult χ ρ : ℝ)) ≤ 1 := by
  set F := (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1) with hF
  have hmem : ∀ ρ ∈ F, ρ ∈ stripZeros χ T ∧ 0 < ρ.im ∧ ρ.im ≤ 1 := by
    intro ρ hρ
    rw [hF, Finset.mem_filter] at hρ
    exact ⟨(stripZeros_finite χ T).mem_toFinset.mp hρ.1, hρ.2⟩
  have hdisk : ∀ ρ ∈ F, ‖ρ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100 := by
    intro ρ hρ
    obtain ⟨hz, hi0, hi1⟩ := hmem ρ hρ
    exact seventeen_low_zero_localized χ hχ hq ρ hz.1 hz.2.1 hz.2.2.1 hi0 hi1
  have hcard : F.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact seventeen_low_zero_unique χ hχ hq a b (hmem a ha).1.1 (hmem b hb).1.1
      (hdisk a ha) (hdisk b hb)
  have hle : ∀ ρ ∈ F, (mult χ ρ : ℝ) ≤ 1 := by
    intro ρ hρ
    exact_mod_cast seventeen_low_zero_simple χ hχ hq ρ (hmem ρ hρ).1.1 (hdisk ρ hρ)
  calc (∑ ρ ∈ F, (mult χ ρ : ℝ)) ≤ ∑ _ρ ∈ F, (1 : ℝ) := Finset.sum_le_sum hle
    _ = (F.card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hcard

end LeanLab.HelfgottMajor.SPLIT_veryLow_level_seventeen_sum_le_one
