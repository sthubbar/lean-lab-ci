import LeanLab.HelfgottMajor.Feed1122VeryLowNoZero

/-!
# Repaired route to `book_count_band_very_low_mult_le`, burst 20261122 S126

The split in `SPLIT_book_count_band_very_low_mult_le` routes the very low band bound through
`very_low_no_zero_of_im_pos_le_one`, which is FALSE at conductor `13`, see the module doc of
`Feed1122VeryLowNoZero`: one primitive character modulo `13` has a simple zero at
`1/2 + 0.8839603… i`. The bound itself survives, since that zero is simple and alone at its
height. This file gives a second twin of `book_count_band_very_low_mult_le`, with exactly its
statement, that avoids the false leaf.

* The real axis carries no strip zero on the band. Proved here, the argument of
  `real_axis_ne_zero_of_band`, which is private in the split file: conductor `1` by the sign of
  `ζ` on `(0, 1)`, conductor at least `2` by `RealAxisKernel.LFunction_ofReal_ne_zero_of_band`.
* Conductor other than `13`: no zero of positive height at most `1`, the S93 assembly
  `very_low_no_zero_of_im_pos_le_one_of_ne_thirteen` from the per conductor leaves.
* Conductor `13`: one LEAF, the zeros of height in `(0, 1]` contribute at most one with
  multiplicity. This is the content of Platt's verification [Pla11] cited in Helfgott,
  arXiv 1305.2897v4, Section 4.6 page 56, for the conductor `13`.

Numerically, burst S126 with mpmath, argument principle on `[10^(-4), 1 - 10^(-4)] × [10^(-6), 1]`
for each of the eleven primitive characters modulo `13`: winding number `1` for the character
with `χ(2) = exp(5πi/6)`, as S93 found, and `0` for the other ten, so the leaf is numerically TRUE.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122VeryLowRepair
open Complex
open LeanLab.HelfgottMajor.ZeroCount1623
open LeanLab.HelfgottMajor.Feed1122VeryLowNoZero

variable {q : ℕ} [NeZero q]

/-- Helper H1, plain-math twin: for a finite set `s` of complex numbers and a multiplicity
function `f : ℂ → ℕ`, the total `∑ f` over `s` is at most `1` whenever `s` is empty or a
singleton whose single value is at most `1`. Concrete instance: `s = {1/2 + 0.8839… i}` and
`f = mult χ` with `f ρ₀ = 1` gives total `1`. Paper page: Helfgott arXiv 1305.2897v4,
Section 4.6 page 56, the conductor `13` count is exactly one simple zero or none. -/
theorem sum_le_one_of_empty_or_singleton {s : Finset ℂ} {f : ℂ → ℕ}
    (h : s = ∅ ∨ ∃ ρ₀, s = {ρ₀} ∧ f ρ₀ ≤ 1) :
    (∑ ρ ∈ s, (f ρ : ℝ)) ≤ 1 := by
  rcases h with h | ⟨ρ₀, hs, hf⟩
  · rw [h]
    simp
  · rw [hs]
    simp
    exact_mod_cast hf

/-- On the band the `L`-function of a primitive character has no zero at a real point of the
open unit interval. Same proof as the private `real_axis_ne_zero_of_band` of the split file. -/
theorem real_axis_ne_zero_of_band' (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  intro σ h0 h1 hL
  by_cases hq : q = 1
  · subst hq
    rw [DirichletCharacter.LFunction_modOne_eq] at hL
    have hneg := (LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg h0 h1).2
    rw [hL] at hneg
    simp at hneg
  · exact LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_of_band χ hχ hT hband
      hq h0 hL

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], the
conductor `13` case of the very low zeros of the band. For a primitive character modulo `13`
and `1 ≤ T` with `13 T ≤ 2πe`, the strip zeros of height in `(0, 1]`, counted with
multiplicity, contribute at most one. Numerically exactly one primitive character modulo `13`
has such a zero, simple, at `1/2 + 0.8839603095… i`, and the other ten have none.
Class HARD: a certified zero count with multiplicity on the rectangle `(0,1) × (0,1]`. -/
theorem veryLow_level_thirteen_sum_le_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1),
      (mult χ ρ : ℝ)) ≤ 1 := by
  subst hq
  refine sum_le_one_of_empty_or_singleton ?_
  -- The residual goal is the certified count kernel: the filtered finset is empty, or a
  -- singleton whose multiplicity is at most one. Attempts made before BLOCKED:
  -- (1) very_low_no_zero_of_im_pos_le_one_of_ne_thirteen needs q ≠ 13, false here.
  -- (2) ZeroCount1623.very_low_count gives only 0.819 * log q + 16.8, about 18.9 at q = 13.
  have hop := very_low_no_zero_of_im_pos_le_one_of_ne_thirteen χ hχ (by omega) hT hband
  obtain ⟨_, hbudget⟩ := ZeroCount1623.very_low_count χ hχ 1 hT
  linarith
  sorry

/-- Twin of `book_count_band_very_low_mult_le`, exactly its statement, from the real axis fact,
the S93 assembly for conductors other than `13`, and the conductor `13` leaf. It does not use the
false leaf `very_low_no_zero_of_im_pos_le_one`. -/
theorem book_count_band_very_low_mult_le_repaired (χ : DirichletCharacter ℂ q)
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
  · have hempty : s.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro ρ hρ ⟨h0, h1⟩
      have := very_low_no_zero_of_im_pos_le_one_of_ne_thirteen χ hχ h13 hT hband ρ
        (hmem ρ hρ) h0
      linarith
    rw [hempty]
    simp

end LeanLab.HelfgottMajor.Feed1122VeryLowRepair
