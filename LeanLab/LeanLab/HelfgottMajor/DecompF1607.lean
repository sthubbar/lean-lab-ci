import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_card

/-!
# Split of `book_count_band_above_one_mult_le_card_level_le_seventeen`, FREE-nv-minimax2 task1607

The target bounds the number of strip zeros of `L(·, χ)` whose imaginary part lies in
`(1, 2πe / q]` by one, for a primitive character `χ` of modulus `q` with `13 ≤ q ≤ 17`.
The band height `2πe / q` is at most `2πe / 13 < 1.32`, so the window is a very short
interval just above height `1`. The proof is a finite verification over the five possible
conductors, and each leaf handles one conductor. The assembly dispatches the five cases
with `omega`. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Conductor thirteen: for a primitive character of modulus exactly `13` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 13]` number at most one, counted
without multiplicity. The window height is below `1.32`, so this is one finite check
over the primitive characters of conductor `13`. -/
theorem book_count_band_above_one_mult_le_card_level_thirteen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 13) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF. Conductor fourteen: for a primitive character of modulus exactly `14` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 14]` number at most one, counted
without multiplicity. The window height is below `1.23`, so this is one finite check
over the primitive characters of conductor `14`. -/
theorem book_count_band_above_one_mult_le_card_level_fourteen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 14) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF. Conductor fifteen: for a primitive character of modulus exactly `15` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 15]` number at most one, counted
without multiplicity. The window height is below `1.15`, so this is one finite check
over the primitive characters of conductor `15`. -/
theorem book_count_band_above_one_mult_le_card_level_fifteen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 15) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF. Conductor sixteen: for a primitive character of modulus exactly `16` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 16]` number at most one, counted
without multiplicity. The window height is below `1.07`, so this is one finite check
over the primitive characters of conductor `16`. -/
theorem book_count_band_above_one_mult_le_card_level_sixteen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 16) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF. Conductor seventeen: for a primitive character of modulus exactly `17` the strip
zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 17]` number at most one, counted
without multiplicity. The window height is below `1.01`, the shortest of the five blocks,
so this is one finite check over the primitive characters of conductor `17`. -/
theorem book_count_band_above_one_mult_le_card_level_seventeen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 17) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- Assembly of the split, FREE-nv-minimax2 task1607. The statement of
`book_count_band_above_one_mult_le_card_level_le_seventeen` character for character,
proved from the five conductor leaves with no gap of its own: the modulus `q` lies in
`{13, 14, 15, 16, 17}`, and each case is dispatched to its leaf. -/
theorem book_count_band_above_one_mult_le_card_level_le_seventeen_F1607 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq13 : 13 ≤ q) (hq17 : q ≤ 17) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have h_cases : q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 := by omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl
  · exact book_count_band_above_one_mult_le_card_level_thirteen_F1607 χ hχ rfl
  · exact book_count_band_above_one_mult_le_card_level_fourteen_F1607 χ hχ rfl
  · exact book_count_band_above_one_mult_le_card_level_fifteen_F1607 χ hχ rfl
  · exact book_count_band_above_one_mult_le_card_level_sixteen_F1607 χ hχ rfl
  · exact book_count_band_above_one_mult_le_card_level_seventeen_F1607 χ hχ rfl

end LeanLab.HelfgottMajor.ZeroCount1623
