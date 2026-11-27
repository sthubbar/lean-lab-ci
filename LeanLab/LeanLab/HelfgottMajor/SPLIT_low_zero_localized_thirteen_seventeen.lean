import LeanLab.HelfgottMajor.ZeroCount1623

/-!
# Split of the localization leaves at conductors `13` and `17`, burst 20261127 S2

The burst S2 split files `SPLIT_veryLow_level_thirteen_sum_le_one` and
`SPLIT_veryLow_level_seventeen_sum_le_one` each carry a localization LEAF,
`thirteen_low_zero_localized` and `seventeen_low_zero_localized`: for `χ` primitive modulo `13`,
respectively `17`, every zero of `L(s, χ)` with `0 < Re s < 1` and `0 < Im s ≤ 1` lies within
`1/100` of `1/2 + 0.88396 i`, respectively `1/2 + 0.39131 i`.

Platt's verification [Pla11], cited in Helfgott arXiv 1305.2897v4 Section 4.6 page 56, gives two
things: GRH for these characters up to the height used, and the location of the zeros on the
critical line. This file splits each localization leaf along those two outputs.

* LEAF GRH step: such a zero has real part `1/2`.
* LEAF critical line step: a zero `1/2 + t i` with `0 < t ≤ 1` has `|t - y₀| < 1/100`, with
  `y₀ = 0.88396`, respectively `0.39131`.

The passage to the disk is PROVED, `norm_sub_of_re_half`. The twins have exactly the statements
of the two localization leaves. Numerically, burst S126 found winding number `0` on
`[10^(-4), 1 - 10^(-4)] × [10^(-6), 1]` for all primitive characters but one at each conductor,
and the one zero found, at each conductor, lies on the critical line. AI wrote this Lean code.
Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SPLIT_low_zero_localized_thirteen_seventeen
open Complex

variable {q : ℕ} [NeZero q]

/-- A point of real part `1/2` is at distance `|Im ρ - y|` from `1/2 + y i`. Proved. -/
theorem norm_sub_of_re_half {ρ : ℂ} {y : ℝ} (hre : ρ.re = 1 / 2) :
    ‖ρ - ⟨1 / 2, y⟩‖ = |ρ.im - y| := by
  have h : ρ - ⟨1 / 2, y⟩ = ((ρ.im - y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11] of GRH,
conductor `13`: for `χ` primitive modulo `13`, a zero of `L(s, χ)` with `0 < Re s < 1` and
`0 < Im s ≤ 1` has `Re s = 1/2`. Class HARD: certified GRH on a box, Turing method. -/
theorem thirteen_low_zero_re_half (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hi0 : 0 < ρ.im) (hi1 : ρ.im ≤ 1) : ρ.re = 1 / 2 := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
critical line step, conductor `13`: for `χ` primitive modulo `13`, a zero `1/2 + t i` of
`L(s, χ)` with `0 < t ≤ 1` has `|t - 0.88396| < 1/100`. Numerically only the character with
`χ(2) = exp(5πi/6)` has such a zero, at `t = 0.8839603095…`.
Class HARD: a certified sign change count of the Hardy type function on `(0, 1]`. -/
theorem thirteen_critical_zero_height (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) (hre : ρ.re = 1 / 2)
    (hi0 : 0 < ρ.im) (hi1 : ρ.im ≤ 1) : |ρ.im - 88396 / 100000| < 1 / 100 := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11] of GRH,
conductor `17`: for `χ` primitive modulo `17`, a zero of `L(s, χ)` with `0 < Re s < 1` and
`0 < Im s ≤ 1` has `Re s = 1/2`. Class HARD: certified GRH on a box, Turing method. -/
theorem seventeen_low_zero_re_half (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hi0 : 0 < ρ.im) (hi1 : ρ.im ≤ 1) : ρ.re = 1 / 2 := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11],
critical line step, conductor `17`: for `χ` primitive modulo `17`, a zero `1/2 + t i` of
`L(s, χ)` with `0 < t ≤ 1` has `|t - 0.39131| < 1/100`. Numerically only the character with
`χ(3) = exp(-5πi/8)` has such a zero, at `t = 0.3913146130…`.
Class HARD: a certified sign change count of the Hardy type function on `(0, 1]`. -/
theorem seventeen_critical_zero_height (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) (hre : ρ.re = 1 / 2)
    (hi0 : 0 < ρ.im) (hi1 : ρ.im ≤ 1) : |ρ.im - 39131 / 100000| < 1 / 100 := by
  sorry

/-- Twin of `SPLIT_veryLow_level_thirteen_sum_le_one.thirteen_low_zero_localized`, exactly its
statement, from the GRH leaf and the critical line leaf. -/
theorem thirteen_low_zero_localized_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hi0 : 0 < ρ.im) (hi1 : ρ.im ≤ 1) :
    ‖ρ - ⟨1 / 2, 88396 / 100000⟩‖ < 1 / 100 := by
  have hre := thirteen_low_zero_re_half χ hχ hq ρ hL h0 h1 hi0 hi1
  rw [norm_sub_of_re_half hre]
  exact thirteen_critical_zero_height χ hχ hq ρ hL hre hi0 hi1

/-- Twin of `SPLIT_veryLow_level_seventeen_sum_le_one.seventeen_low_zero_localized`, exactly its
statement, from the GRH leaf and the critical line leaf. -/
theorem seventeen_low_zero_localized_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) (ρ : ℂ) (hL : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hi0 : 0 < ρ.im) (hi1 : ρ.im ≤ 1) :
    ‖ρ - ⟨1 / 2, 39131 / 100000⟩‖ < 1 / 100 := by
  have hre := seventeen_low_zero_re_half χ hχ hq ρ hL h0 h1 hi0 hi1
  rw [norm_sub_of_re_half hre]
  exact seventeen_critical_zero_height χ hχ hq ρ hL hre hi0 hi1

end LeanLab.HelfgottMajor.SPLIT_low_zero_localized_thirteen_seventeen
