import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_card
import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_one

/-!
# Feed1122 split of the open conductor block leaves of the band above height one

This file splits the open leaves of `SPLIT_book_count_band_above_one_mult_le_card` and
`SPLIT_book_count_band_above_one_mult_le_one`, the counting half and the pointwise
multiplicity half of the band count of P0014 page 38 display 4.26, as used in the band
`1 ≤ T`, `q * T ≤ 2πe` of the zero count `book_zero_count` (P0014 Part IV pages 431 and 432,
display 16.21).

* Each conductor block is cut into single conductors. The conductors `2`, `6` and `10`, like
  `14`, carry no primitive character at all, since every character of modulus `2m` with `m`
  odd factors through modulus `m`. Those cases are proved here by `decide` on the unit groups,
  so the remaining leaves are the genuine conductors `3, 4, 5, 7, 8, 9, 11, 12` and, for the
  multiplicity half, `13, 15, 16, 17`.
* The conductor one leaves are about the Riemann zeta function on `(1, 2πe]`, `2πe < 17.08`.
  They are cut at height `14`: one shared leaf says there is no zeta zero of the strip with
  imaginary part in `(1, 14)`, the first zero sitting at `14.1347…`, and the other leaves speak
  only about the zeros with imaginary part in `[14, 2πe]`.
* The counting leaf of the block `13` to `17` is already split on main in `DecompF1607.lean`,
  with the conductor `14` proved there, so it is not split again here.

Every remaining leaf is a rigorous verification of the low zeros of one `L`-function, which
is the class HARD. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122BandAboveOne
open LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- A character of modulus `n` is not primitive when the reduction of unit groups to a proper
divisor `d` of `n` is injective: then the character factors through `d`, so its conductor is
at most `d < n`. Proved, no input. -/
private lemma not_primitive_of_unitsMap_injective {n d : ℕ} [NeZero n] (hd : d ∣ n) (hlt : d < n)
    (hi : Function.Injective (ZMod.unitsMap hd)) (χ : DirichletCharacter ℂ n) :
    ¬ χ.IsPrimitive := by
  have hf : χ.FactorsThrough d := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
    intro x hx
    have hx1 : x = 1 := hi (by simpa using hx)
    rw [hx1]
    exact map_one χ.toUnitHom
  have hc : χ.conductor ≤ d := Nat.sInf_le hf
  intro hχ
  change χ.conductor = n at hχ
  omega

/-- No primitive character of modulus `2`; it factors through modulus `1`. Proved. -/
private lemma not_primitive_two (χ : DirichletCharacter ℂ 2) : ¬ χ.IsPrimitive :=
  not_primitive_of_unitsMap_injective (show 1 ∣ 2 by norm_num) (by norm_num) (by decide) χ

/-- No primitive character of modulus `6`; it factors through modulus `3`. Proved. -/
private lemma not_primitive_six (χ : DirichletCharacter ℂ 6) : ¬ χ.IsPrimitive :=
  not_primitive_of_unitsMap_injective (show 3 ∣ 6 by norm_num) (by norm_num) (by decide) χ

/-- No primitive character of modulus `10`; it factors through modulus `5`. Proved. -/
private lemma not_primitive_ten (χ : DirichletCharacter ℂ 10) : ¬ χ.IsPrimitive :=
  not_primitive_of_unitsMap_injective (show 5 ∣ 10 by norm_num) (by norm_num) (by decide) χ

/-- No primitive character of modulus `14`; it factors through modulus `7`. Proved. -/
private lemma not_primitive_fourteen (χ : DirichletCharacter ℂ 14) : ¬ χ.IsPrimitive :=
  not_primitive_of_unitsMap_injective (show 7 ∣ 14 by norm_num) (by norm_num) (by decide) χ

/-! ## Conductor one: the zeta function on `(1, 2πe]` -/

/-- LEAF: conductor one, zeta has no strip zero with imaginary part in `(1, 14)`. HARD.
For the primitive character of modulus `1`, whose `L`-function is the Riemann zeta function,
every zero of the open strip with absolute imaginary part at most `2πe` and imaginary part
above `1` has imaginary part at least `14`. This is the band of P0014 page 38 display 4.26 at
`q = 1`, read against the standard zero tables: the first zeta zero is at `14.1347…`. -/
theorem zeta_band_no_zero_below_fourteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 1) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1), 1 < ρ.im → 14 ≤ ρ.im := by
  sorry

/-- LEAF: conductor one, at most one zeta zero with imaginary part in `[14, 2πe]`. HARD.
For the primitive character of modulus `1` the strip zeros with absolute imaginary part at
most `2πe < 17.08` and imaginary part at least `14` number at most one, counted without
multiplicity. P0014 page 38 display 4.26 at `q = 1`; the zeta zeros below `21` are
`14.1347…` and then `21.0220…`, so the window holds only the first. -/
theorem zeta_band_card_from_fourteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 1) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1)).toFinset.filter
      (fun ρ => 14 ≤ ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF: conductor one, a zeta zero with imaginary part in `[14, 2πe]` is simple. HARD.
For the primitive character of modulus `1` every strip zero with absolute imaginary part at
most `2πe` and imaginary part at least `14` has multiplicity at most one. P0014 page 38
display 4.26 at `q = 1`; this is the simplicity of the first zeta zero `14.1347…`. -/
theorem zeta_band_mult_from_fourteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 1) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1), 14 ≤ ρ.im → (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- Twin of `book_count_band_above_one_mult_le_card_level_one`, same statement, assembled from
the two conductor one leaves: the window above height `1` sits above height `14`. -/
theorem book_count_band_above_one_mult_le_card_level_one_feed1122 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 1) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  refine le_trans (Finset.card_le_card ?_) (zeta_band_card_from_fourteen χ hχ hq)
  intro ρ hρ
  have hp := Finset.mem_filter.mp hρ
  have hz := (stripZeros_finite χ (2 * Real.pi * Real.exp 1)).mem_toFinset.mp hp.1
  exact Finset.mem_filter.mpr ⟨hp.1, zeta_band_no_zero_below_fourteen χ hχ hq ρ hz hp.2.2⟩

/-- Twin of `book_count_band_above_one_mult_le_one_level_one`, same statement, assembled from
the two conductor one leaves: a zero above height `1` sits above height `14`. -/
theorem book_count_band_above_one_mult_le_one_level_one_feed1122 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 1) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  intro ρ hρ
  have hp := Finset.mem_filter.mp hρ
  have hz := (stripZeros_finite χ (2 * Real.pi * Real.exp 1)).mem_toFinset.mp hp.1
  exact zeta_band_mult_from_fourteen χ hχ hq ρ hz
    (zeta_band_no_zero_below_fourteen χ hχ hq ρ hz hp.2.2)

/-! ## Counting half, conductors two to seventeen -/

/-- Conductor `2` carries no primitive character, so this case is empty. Proved. -/
theorem band_above_one_card_level_two (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 2) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  subst hq
  exact absurd hχ (not_primitive_two χ)

/-- LEAF: conductor `3`, the count of the band window above height one. HARD.
For a primitive character of modulus exactly `3` the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 3]` number at most one,
counted without multiplicity. The window height
`2πe / 3` is below `5.70`. P0014 page 38 display 4.26 at `q = 3`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `3`. -/
theorem band_above_one_card_level_three (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 3) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF: conductor `4`, the count of the band window above height one. HARD.
For a primitive character of modulus exactly `4` the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 4]` number at most one,
counted without multiplicity. The window height
`2πe / 4` is below `4.27`. P0014 page 38 display 4.26 at `q = 4`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `4`. -/
theorem band_above_one_card_level_four (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 4) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF: conductor `5`, the count of the band window above height one. HARD.
For a primitive character of modulus exactly `5` the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 5]` number at most one,
counted without multiplicity. The window height
`2πe / 5` is below `3.42`. P0014 page 38 display 4.26 at `q = 5`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `5`. -/
theorem band_above_one_card_level_five (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 5) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- Conductor `6` carries no primitive character, so this case is empty. Proved. -/
theorem band_above_one_card_level_six (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 6) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  subst hq
  exact absurd hχ (not_primitive_six χ)

/-- Twin of `book_count_band_above_one_mult_le_card_level_le_six`, same statement, assembled from the single conductor
cases `2` to `6` by a case split on `q`. -/
theorem book_count_band_above_one_mult_le_card_level_le_six_feed1122 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 2 ≤ q) (hhi : q ≤ 6) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have h_cases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 := by omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl
  · exact band_above_one_card_level_two χ hχ rfl
  · exact band_above_one_card_level_three χ hχ rfl
  · exact band_above_one_card_level_four χ hχ rfl
  · exact band_above_one_card_level_five χ hχ rfl
  · exact band_above_one_card_level_six χ hχ rfl

/-- LEAF: conductor `7`, the count of the band window above height one. HARD.
For a primitive character of modulus exactly `7` the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 7]` number at most one,
counted without multiplicity. The window height
`2πe / 7` is below `2.44`. P0014 page 38 display 4.26 at `q = 7`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `7`. -/
theorem band_above_one_card_level_seven (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 7) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF: conductor `8`, the count of the band window above height one. HARD.
For a primitive character of modulus exactly `8` the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 8]` number at most one,
counted without multiplicity. The window height
`2πe / 8` is below `2.14`. P0014 page 38 display 4.26 at `q = 8`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `8`. -/
theorem band_above_one_card_level_eight (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 8) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF: conductor `9`, the count of the band window above height one. HARD.
For a primitive character of modulus exactly `9` the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 9]` number at most one,
counted without multiplicity. The window height
`2πe / 9` is below `1.90`. P0014 page 38 display 4.26 at `q = 9`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `9`. -/
theorem band_above_one_card_level_nine (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 9) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- Conductor `10` carries no primitive character, so this case is empty. Proved. -/
theorem band_above_one_card_level_ten (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 10) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  subst hq
  exact absurd hχ (not_primitive_ten χ)

/-- LEAF: conductor `11`, the count of the band window above height one. HARD.
For a primitive character of modulus exactly `11` the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 11]` number at most one,
counted without multiplicity. The window height
`2πe / 11` is below `1.56`. P0014 page 38 display 4.26 at `q = 11`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `11`. -/
theorem band_above_one_card_level_eleven (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 11) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF: conductor `12`, the count of the band window above height one. HARD.
For a primitive character of modulus exactly `12` the strip zeros of `L(·, χ)` with imaginary part in `(1, 2πe / 12]` number at most one,
counted without multiplicity. The window height
`2πe / 12` is below `1.43`. P0014 page 38 display 4.26 at `q = 12`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `12`. -/
theorem band_above_one_card_level_twelve (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 12) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- Twin of `book_count_band_above_one_mult_le_card_level_le_twelve`, same statement, assembled from the single conductor
cases `7` to `12` by a case split on `q`. -/
theorem book_count_band_above_one_mult_le_card_level_le_twelve_feed1122 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 7 ≤ q) (hhi : q ≤ 12) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have h_cases : q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 := by omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact band_above_one_card_level_seven χ hχ rfl
  · exact band_above_one_card_level_eight χ hχ rfl
  · exact band_above_one_card_level_nine χ hχ rfl
  · exact band_above_one_card_level_ten χ hχ rfl
  · exact band_above_one_card_level_eleven χ hχ rfl
  · exact band_above_one_card_level_twelve χ hχ rfl

/-! ## Multiplicity half, conductors two to seventeen -/

/-- Conductor `2` carries no primitive character, so this case is empty. Proved. -/
theorem band_above_one_mult_level_two (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 2) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  subst hq
  exact absurd hχ (not_primitive_two χ)

/-- LEAF: conductor `3`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `3` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 3]` has multiplicity
at most one. The window height
`2πe / 3` is below `5.70`. P0014 page 38 display 4.26 at `q = 3`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `3`. -/
theorem band_above_one_mult_level_three (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 3) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: conductor `4`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `4` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 4]` has multiplicity
at most one. The window height
`2πe / 4` is below `4.27`. P0014 page 38 display 4.26 at `q = 4`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `4`. -/
theorem band_above_one_mult_level_four (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 4) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: conductor `5`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `5` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 5]` has multiplicity
at most one. The window height
`2πe / 5` is below `3.42`. P0014 page 38 display 4.26 at `q = 5`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `5`. -/
theorem band_above_one_mult_level_five (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 5) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- Conductor `6` carries no primitive character, so this case is empty. Proved. -/
theorem band_above_one_mult_level_six (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 6) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  subst hq
  exact absurd hχ (not_primitive_six χ)

/-- Twin of `book_count_band_above_one_mult_le_one_level_le_six`, same statement, assembled from the single conductor
cases `2` to `6` by a case split on `q`. -/
theorem book_count_band_above_one_mult_le_one_level_le_six_feed1122 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 2 ≤ q) (hhi : q ≤ 6) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  have h_cases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 := by omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl
  · exact band_above_one_mult_level_two χ hχ rfl
  · exact band_above_one_mult_level_three χ hχ rfl
  · exact band_above_one_mult_level_four χ hχ rfl
  · exact band_above_one_mult_level_five χ hχ rfl
  · exact band_above_one_mult_level_six χ hχ rfl

/-- LEAF: conductor `7`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `7` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 7]` has multiplicity
at most one. The window height
`2πe / 7` is below `2.44`. P0014 page 38 display 4.26 at `q = 7`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `7`. -/
theorem band_above_one_mult_level_seven (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 7) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: conductor `8`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `8` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 8]` has multiplicity
at most one. The window height
`2πe / 8` is below `2.14`. P0014 page 38 display 4.26 at `q = 8`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `8`. -/
theorem band_above_one_mult_level_eight (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 8) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: conductor `9`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `9` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 9]` has multiplicity
at most one. The window height
`2πe / 9` is below `1.90`. P0014 page 38 display 4.26 at `q = 9`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `9`. -/
theorem band_above_one_mult_level_nine (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 9) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- Conductor `10` carries no primitive character, so this case is empty. Proved. -/
theorem band_above_one_mult_level_ten (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 10) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  subst hq
  exact absurd hχ (not_primitive_ten χ)

/-- LEAF: conductor `11`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `11` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 11]` has multiplicity
at most one. The window height
`2πe / 11` is below `1.56`. P0014 page 38 display 4.26 at `q = 11`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `11`. -/
theorem band_above_one_mult_level_eleven (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 11) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: conductor `12`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `12` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 12]` has multiplicity
at most one. The window height
`2πe / 12` is below `1.43`. P0014 page 38 display 4.26 at `q = 12`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `12`. -/
theorem band_above_one_mult_level_twelve (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 12) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- Twin of `book_count_band_above_one_mult_le_one_level_le_twelve`, same statement, assembled from the single conductor
cases `7` to `12` by a case split on `q`. -/
theorem book_count_band_above_one_mult_le_one_level_le_twelve_feed1122 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 7 ≤ q) (hhi : q ≤ 12) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  have h_cases : q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 := by omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact band_above_one_mult_level_seven χ hχ rfl
  · exact band_above_one_mult_level_eight χ hχ rfl
  · exact band_above_one_mult_level_nine χ hχ rfl
  · exact band_above_one_mult_level_ten χ hχ rfl
  · exact band_above_one_mult_level_eleven χ hχ rfl
  · exact band_above_one_mult_level_twelve χ hχ rfl

/-- LEAF: conductor `13`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `13` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 13]` has multiplicity
at most one. The window height
`2πe / 13` is below `1.32`. P0014 page 38 display 4.26 at `q = 13`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `13`. -/
theorem band_above_one_mult_level_thirteen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 13) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- Conductor `14` carries no primitive character, so this case is empty. Proved. -/
theorem band_above_one_mult_level_fourteen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 14) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  subst hq
  exact absurd hχ (not_primitive_fourteen χ)

/-- LEAF: conductor `15`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `15` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 15]` has multiplicity
at most one. The window height
`2πe / 15` is below `1.14`. P0014 page 38 display 4.26 at `q = 15`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `15`. -/
theorem band_above_one_mult_level_fifteen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 15) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: conductor `16`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `16` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 16]` has multiplicity
at most one. The window height
`2πe / 16` is below `1.07`. P0014 page 38 display 4.26 at `q = 16`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `16`. -/
theorem band_above_one_mult_level_sixteen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 16) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF: conductor `17`, the multiplicity of the band window above height one. HARD.
For a primitive character of modulus exactly `17` every strip zero of `L(·, χ)` with imaginary part in `(1, 2πe / 17]` has multiplicity
at most one. The window height
`2πe / 17` is below `1.01`. P0014 page 38 display 4.26 at `q = 17`, as used in the band
of P0014 Part IV page 431; a rigorous low zero verification for the primitive characters of
conductor `17`. -/
theorem band_above_one_mult_level_seventeen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 17) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- Twin of `book_count_band_above_one_mult_le_one_level_le_seventeen`, same statement, assembled from the single conductor
cases `13` to `17` by a case split on `q`. -/
theorem book_count_band_above_one_mult_le_one_level_le_seventeen_feed1122 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hlo : 13 ≤ q) (hhi : q ≤ 17) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  have h_cases : q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 := by omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl
  · exact band_above_one_mult_level_thirteen χ hχ rfl
  · exact band_above_one_mult_level_fourteen χ hχ rfl
  · exact band_above_one_mult_level_fifteen χ hχ rfl
  · exact band_above_one_mult_level_sixteen χ hχ rfl
  · exact band_above_one_mult_level_seventeen χ hχ rfl

end LeanLab.HelfgottMajor.Feed1122BandAboveOne
