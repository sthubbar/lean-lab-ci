import LeanLab.HelfgottMajor.ZeroCount1623

/-!
# Split of the simplicity leaves at conductors `13` and `17`, burst 20261127 S2

The burst S2 split files `SPLIT_veryLow_level_thirteen_sum_le_one` and
`SPLIT_veryLow_level_seventeen_sum_le_one` each carry a simplicity LEAF,
`thirteen_low_zero_simple` and `seventeen_low_zero_simple`: a zero of `L(s, χ)`, `χ` primitive
modulo `13` or `17`, within `1/100` of `1/2 + 0.88396 i`, respectively `1/2 + 0.39131 i`, has
multiplicity at most one. Platt [Pla11], cited in Helfgott arXiv 1305.2897v4 Section 4.6 page 56,
certifies simplicity of an isolated zero through the nonvanishing of `L'`. This file splits off
that numerical input as one LEAF per conductor, `deriv L(·, χ) ρ ≠ 0`, and proves the passage
from a nonzero derivative to multiplicity one in Lean, `mult_le_one_of_deriv_ne_zero`, by
Mathlib's `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`.

The twins `thirteen_low_zero_simple_of_leaves` and `seventeen_low_zero_simple_of_leaves` have
exactly the statements of the two leaves. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SPLIT_low_zero_simple_thirteen_seventeen
open Complex
open LeanLab.HelfgottMajor.ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- A zero `ρ ≠ 1` of `L(s, χ)` at which the derivative does not vanish has multiplicity at most
one. Proved, by analyticity of `L(s, χ)` off `s = 1`. -/
theorem mult_le_one_of_deriv_ne_zero (χ : DirichletCharacter ℂ q) (ρ : ℂ) (hρ : ρ ≠ 1)
    (hL : DirichletCharacter.LFunction χ ρ = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) ρ ≠ 0) : mult χ ρ ≤ 1 := by
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | s ≠ 1} :=
    fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    hdiff.analyticAt (hopen.mem_nhds hρ)
  have h1 := han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hL hd
  simp [mult, analyticOrderNatAt, h1]

/-- A point within `1/100` of `1/2 + y i` is not `1`. -/
theorem ne_one_of_near_half {ρ c : ℂ} (hc : c.re = 1 / 2) (hd : ‖ρ - c‖ < 1 / 100) : ρ ≠ 1 := by
  rintro rfl
  have h := (Complex.abs_re_le_norm (1 - c)).trans_lt hd
  rw [sub_re, one_re, hc, abs_of_pos (by norm_num)] at h
  norm_num at h

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
simplicity step for conductor `13`: for `χ` primitive modulo `13`, `L'(ρ, χ) ≠ 0` at every zero
`ρ` of `L(s, χ)` within `1/100` of `1/2 + 0.88396 i`. Numerically, burst 20261127 S2 with
mpmath, the only such zero is `1/2 + 0.8839603095… i`, for the character with
`χ(2) = exp(5πi/6)`, and `|L'(ρ, χ)| ≈ 0.877` there.
Class MEDIUM: a certified lower bound for `|L'|` on an enclosure of the zero. -/
theorem thirteen_low_zero_deriv_ne_zero (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0)
    (hd : ‖ρ - ⟨1 / 2, 88396 / 100000⟩‖ < 1 / 100) :
    deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
simplicity step for conductor `17`: for `χ` primitive modulo `17`, `L'(ρ, χ) ≠ 0` at every zero
`ρ` of `L(s, χ)` within `1/100` of `1/2 + 0.39131 i`. Numerically, burst 20261127 S2 with
mpmath, the only such zero is `1/2 + 0.3913146130… i`, for the character with
`χ(3) = exp(-5πi/8)`, and `|L'(ρ, χ)| ≈ 0.837` there.
Class MEDIUM: a certified lower bound for `|L'|` on an enclosure of the zero. -/
theorem seventeen_low_zero_deriv_ne_zero (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0)
    (hd : ‖ρ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100) :
    deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
  sorry

/-- Twin of `SPLIT_veryLow_level_thirteen_sum_le_one.thirteen_low_zero_simple`, exactly its
statement, from the derivative leaf and `mult_le_one_of_deriv_ne_zero`. -/
theorem thirteen_low_zero_simple_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0)
    (hd : ‖ρ - ⟨1 / 2, 88396 / 100000⟩‖ < 1 / 100) : mult χ ρ ≤ 1 :=
  mult_le_one_of_deriv_ne_zero χ ρ (ne_one_of_near_half rfl hd) hL
    (thirteen_low_zero_deriv_ne_zero χ hχ hq ρ hL hd)

/-- Twin of `SPLIT_veryLow_level_seventeen_sum_le_one.seventeen_low_zero_simple`, exactly its
statement, from the derivative leaf and `mult_le_one_of_deriv_ne_zero`. -/
theorem seventeen_low_zero_simple_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0)
    (hd : ‖ρ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100) : mult χ ρ ≤ 1 :=
  mult_le_one_of_deriv_ne_zero χ ρ (ne_one_of_near_half rfl hd) hL
    (seventeen_low_zero_deriv_ne_zero χ hχ hq ρ hL hd)

end LeanLab.HelfgottMajor.SPLIT_low_zero_simple_thirteen_seventeen
