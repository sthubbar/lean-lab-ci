import LeanLab.HelfgottMajor.DecompF1607

/-!
# Split of the conductor seventeen zero-count leaf

This file splits the conductor seventeen instance into arithmetic bounds for the height and a
finite contour count split according to the parity of the character. The rational upper
endpoint makes the contour data independent of the transcendental endpoint.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623

open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Arithmetic step for the lower end of the conductor seventeen window. The exact
endpoint `2 pi e / 17` is greater than `1`, so the window is not empty by its lower
endpoint alone. -/
theorem window_height_lower_F2869 :
    1 < 2 * Real.pi * Real.exp 1 / 17 := by
  have hp := Real.pi_gt_d4
  have he := Real.exp_one_gt_d9
  have hp0 := Real.pi_pos
  have he0 := Real.exp_pos 1
  have hnum : 17 < 2 * Real.pi * Real.exp 1 := by
    nlinarith
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 17)]
  exact hnum

/-- LEAF. Arithmetic step for the upper end of the conductor seventeen window. The exact
endpoint `2 pi e / 17` is below the rational number `101 / 100`, which is used as the
top of the contour rectangle. -/
theorem window_height_upper_F2869 :
    2 * Real.pi * Real.exp 1 / 17 < 101 / 100 := by
  have hp := Real.pi_lt_d4
  have he := Real.exp_one_lt_d9
  have hp0 := Real.pi_pos
  have he0 := Real.exp_pos 1
  have hnum : 2 * Real.pi * Real.exp 1 < 17.08 := by
    nlinarith
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 17)]
  nlinarith

/-- LEAF. Finite contour step for the even primitive characters of modulus seventeen.
On the rational rectangle with vertical interval `(1, 101 / 100]`, the `L`-function has at
most one strip zero. The rectangle and its boundary data are fixed rational numbers, so
this is a finite contour calculation for the even characters. -/
theorem rational_window_count_le_one_even_F2869 (χ : DirichletCharacter ℂ 17)
    (hχ : χ.IsPrimitive) (heven : χ.Even) :
    ((stripZeros_finite χ (101 / 100)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF. Finite contour step for the odd primitive characters of modulus seventeen.
On the rational rectangle with vertical interval `(1, 101 / 100]`, the `L`-function has at
most one strip zero. The rectangle and its boundary data are fixed rational numbers, so
this is a finite contour calculation for the odd characters. -/
theorem rational_window_count_le_one_odd_F2869 (χ : DirichletCharacter ℂ 17)
    (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    ((stripZeros_finite χ (101 / 100)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- Assembly of the conductor seventeen split. The exact window lies in the rational
window by the height estimate. The parity split gives the rational-window count, and
cardinality monotonicity gives the exact-window count. -/
theorem book_count_band_above_one_mult_le_card_level_seventeen_F1607_F2869 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 17) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  subst hq
  have hupper := window_height_upper_F2869
  have hsubset :
      (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (17 : ℝ))).toFinset.filter
          (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) ⊆
        (stripZeros_finite χ (101 / 100)).toFinset.filter
          (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) := by
    intro ρ hρ
    have hp := Finset.mem_filter.mp hρ
    have hz := (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (17 : ℝ))).mem_toFinset.mp hp.1
    apply Finset.mem_filter.mpr
    refine ⟨(stripZeros_finite χ (101 / 100)).mem_toFinset.mpr
      ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans (le_of_lt hupper)⟩, hp.2⟩
  have hcard := Finset.card_le_card hsubset
  rcases χ.even_or_odd with heven | hodd
  · exact hcard.trans (rational_window_count_le_one_even_F2869 χ hχ heven)
  · exact hcard.trans (rational_window_count_le_one_odd_F2869 χ hχ hodd)

end LeanLab.HelfgottMajor.ZeroCount1623
