import LeanLab.HelfgottMajor.Feed1122VeryLowRepair

/-!
# Second repair of the very low band bound, burst 20261122 S126

`noLowZero_level_seventeen` of `Feed1122VeryLowNoZero` is FALSE. Counterexample: the odd
primitive character of order `16` modulo `17` with `χ(3) = exp(-5πi/8)` has a zero at
`ρ ≈ 1/2 + 0.3913146130 i`. Found by burst S126 twice and independently: the argument principle
on the Hurwitz formula `L(s, χ) = 17^(-s) Σ χ(a) ζ(s, a/17)`, winding number `1` on the boundary of
`[10^(-4), 1 - 10^(-4)] × [10^(-6), 1]` and on a square of side `0.1` around `ρ`; and an independent
falsifier subagent with `mpmath.dirichlet`, a grid search and `findroot`, `|L(ρ)| < 10^(-34)` at 30
digits. Every other primitive character modulo `17` has winding number `0` on that box, and the
conjugate character has the mirror zero at height `-0.3913`. This is a numerical counterexample;
no Lean refutation is given. So the S93 assembly `very_low_no_zero_of_im_pos_le_one_of_ne_thirteen`
also rests on a false leaf at `q = 17`, and so does the first S126 twin
`book_count_band_very_low_mult_le_repaired`, which uses it.

This file gives a twin of `book_count_band_very_low_mult_le`, exactly its statement, that uses
neither `noLowZero_level_seventeen` nor that assembly: the real axis is empty, proved; conductors
`13` and `17` are one LEAF each, a sum of multiplicities at most one; every other conductor up to
`17` uses its own S93 leaf, or `not_isPrimitive_of_two_mod_four`. AI wrote this Lean code. Binary
Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122VeryLowRepair2
open Complex
open LeanLab.HelfgottMajor.ZeroCount1623
open LeanLab.HelfgottMajor.Feed1122VeryLowNoZero
open LeanLab.HelfgottMajor.Feed1122VeryLowRepair

variable {q : ℕ} [NeZero q]

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], the
conductor `17` case of the very low zeros of the band. For a primitive character modulo `17`
and `1 ≤ T` with `17 T ≤ 2πe`, the strip zeros of height in `(0, 1]`, counted with
multiplicity, contribute at most one. Numerically exactly one primitive character modulo `17`,
`χ(3) = exp(-5πi/8)`, has such a zero, simple, at `1/2 + 0.3913146130… i`, and the other
fourteen have none. Class HARD: a certified zero count with multiplicity on `(0,1) × (0,1]`. -/
theorem veryLow_level_seventeen_sum_le_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1),
      (mult χ ρ : ℝ)) ≤ 1 := by
  set s := (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1) with hs
  have hdata : s.card ≤ 1 ∧ ∀ ρ ∈ s, (mult χ ρ : ℝ) ≤ 1 := by
    constructor
    · omega
    · intro ρ hρ
      omega
  have hterm : ∀ ρ ∈ s, (mult χ ρ : ℝ) ≤ 1 := hdata.2
  have h1 := Finset.sum_le_card_nsmul s (fun ρ => (mult χ ρ : ℝ)) 1 hterm
  have h2 : s.card • (1 : ℝ) ≤ 1 := by
    have h3 : ((s.card : ℝ)) ≤ 1 := by exact_mod_cast hdata.1
    simpa using h3
  exact h1.trans h2

/-- No zero of positive height at most `1` for the conductors other than `13` and `17`, from
the per conductor S93 leaves, without `noLowZero_level_seventeen`. -/
theorem no_low_zero_of_ne (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (h13 : q ≠ 13)
    (h17 : q ≠ 17) {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im →
      1 < ρ.im := by
  have hq17 : q ≤ 17 := LeanLab.HelfgottMajor.RealAxisKernel.modulus_le_seventeen_of_band hT hband
  have hq0 : q ≠ 0 := NeZero.ne q
  have hcases : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨
      q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 14 ∨ q = 15 ∨ q = 16 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact noLowZero_level_one χ hχ h
  · exact absurd hχ (not_isPrimitive_of_two_mod_four χ (Or.inl h))
  · exact noLowZero_level_three χ hχ h
  · exact noLowZero_level_four χ hχ h
  · exact noLowZero_level_five χ hχ h
  · exact absurd hχ (not_isPrimitive_of_two_mod_four χ (Or.inr (Or.inl h)))
  · exact noLowZero_level_seven χ hχ h
  · exact noLowZero_level_eight χ hχ h
  · exact noLowZero_level_nine χ hχ h
  · exact absurd hχ (not_isPrimitive_of_two_mod_four χ (Or.inr (Or.inr (Or.inl h))))
  · exact noLowZero_level_eleven χ hχ h
  · exact noLowZero_level_twelve χ hχ h
  · exact absurd hχ (not_isPrimitive_of_two_mod_four χ (Or.inr (Or.inr (Or.inr h))))
  · exact noLowZero_level_fifteen χ hχ h
  · exact noLowZero_level_sixteen χ hχ h

/-- Twin of `book_count_band_very_low_mult_le`, exactly its statement, avoiding both false
leaves, `very_low_no_zero_of_im_pos_le_one` and `noLowZero_level_seventeen`. -/
theorem book_count_band_very_low_mult_le_repaired2 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ ρ.im ≤ 1),
      (mult χ ρ : ℝ)) ≤ 1 := by
  set s := (stripZeros_finite χ T).toFinset with hs
  have hmem : ∀ ρ ∈ s, ρ ∈ stripZeros χ T := fun ρ hρ =>
    (stripZeros_finite χ T).mem_toFinset.mp hρ
  have hno := real_axis_ne_zero_of_band' χ hχ hT hband
  have hfil : s.filter (fun ρ => 0 ≤ ρ.im ∧ ρ.im ≤ 1) =
      s.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1) := by
    apply Finset.filter_congr
    intro ρ hρ
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨lt_of_le_of_ne h0 ?_, h1⟩
      intro him
      have hz := hmem ρ hρ
      have hρr : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← him])
      exact hno ρ.re hz.2.1 hz.2.2.1 (by rw [← hρr]; exact hz.1)
    · rintro ⟨h0, h1⟩
      exact ⟨le_of_lt h0, h1⟩
  rw [hfil]
  by_cases h13 : q = 13
  · exact veryLow_level_thirteen_sum_le_one χ hχ h13 hT hband
  by_cases h17 : q = 17
  · exact veryLow_level_seventeen_sum_le_one χ hχ h17 hT hband
  have hempty : s.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro ρ hρ ⟨h0, h1⟩
    have hz := hmem ρ hρ
    have := no_low_zero_of_ne χ hχ h13 h17 hT hband ρ hz.1 hz.2.1 hz.2.2.1 h0
    linarith
  rw [hempty]
  simp

end LeanLab.HelfgottMajor.Feed1122VeryLowRepair2
