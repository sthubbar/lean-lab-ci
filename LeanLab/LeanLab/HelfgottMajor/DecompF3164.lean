import LeanLab.HelfgottMajor.DecompF1607
import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_card
import LeanLab.HelfgottMajor.ZeroCount1623

/-!
# Split of `book_count_band_above_one_mult_le_card_level_sixteen_F1607`, FREE-nv-step task3164

The target bounds the number of strip zeros of `L(·, χ)` whose imaginary part lies in
`(1, 2πe / 16]` by one, for a primitive character `χ` of modulus `q` with `q = 16`.
The band height `2πe / 16` is approximately `1.07`, so the window is a very short
interval just above height `1`. The proof is a finite verification over the eight primitive
characters of conductor `16`. Each leaf handles one aspect of the verification. The assembly
dispatches to the leaves and uses the arithmetic bound on the height. AI wrote this Lean code.
Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Arithmetic bound: the top height of the band for conductor sixteen is strictly
below `1.07`. This is a purely numerical inequality about `π` and `e`. -/
theorem LEAF_height_bound_sixteen_F3164 :
    (2 : ℝ) * Real.pi * Real.exp 1 / 16 < 1.07 := by
  have hpi_gt : Real.pi > 3.1415 := by
    have := Real.pi_gt_d4
    norm_num at this ⊢
    <;> linarith
  have hpi_lt : Real.pi < 3.1416 := by
    have := Real.pi_lt_d4
    norm_num at this ⊢
    <;> linarith
  have hexp_gt : Real.exp 1 > 2.718281828 := by
    have := Real.exp_one_gt_d9
    norm_num at this ⊢
    <;> linarith
  have hexp_lt : Real.exp 1 < 2.718281829 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    <;> linarith
  have h_main : (2 : ℝ) * Real.pi * Real.exp 1 / 16 < 1.07 := by
    have h₁ : (2 : ℝ) * Real.pi * Real.exp 1 / 16 < 1.07 := by
      have h₂ : Real.pi < 3.1416 := hpi_lt
      have h₃ : Real.exp 1 < 2.718281829 := hexp_lt
      have h₄ : (2 : ℝ) * Real.pi * Real.exp 1 / 16 < 1.07 := by
        norm_num at h₂ h₃ ⊢
        <;> nlinarith [Real.pi_pos, Real.exp_pos 1]
      exact h₄
    exact h₁
  exact h_main

/-- LEAF. Zero-free window for all primitive characters modulo sixteen: the window
`(1, 2πe / 16]` contains no strip zero of `L(s, χ)` for any primitive character of
conductor `16`. This is a finite verification over the eight primitive characters. -/
theorem LEAF_window_empty_sixteen_F3164 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 16) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  sorry

/-- Assembly of the split for conductor sixteen, FREE-nv-step task3164. The statement of
`book_count_band_above_one_mult_le_card_level_sixteen_F1607` character for character,
proved from the leaves with no gap of its own: the height bound gives the numerical context,
and the window lemma shows the filtered zero set is empty for each primitive character. -/
theorem book_count_band_above_one_mult_le_card_level_sixteen_F1607_F3164 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 16) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have h₁ : (2 : ℝ) * Real.pi * Real.exp 1 / 16 < 1.07 := LEAF_height_bound_sixteen_F3164
  have h₂ : (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ :=
    LEAF_window_empty_sixteen_F3164 χ hχ hq
  rw [h₂]
  <;> simp

end LeanLab.HelfgottMajor.ZeroCount1623