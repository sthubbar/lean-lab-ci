import LeanLab.HelfgottMajor.Feed1122BandAboveOne
import LeanLab.HelfgottMajor.DecompF1607

/-!
# S125 re-split of the conductor leaves of the band above height one

`Feed1122BandAboveOne.lean` and `DecompF1607.lean` leave, for each conductor
`q ∈ {3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 17}`, one or two HARD leaves about the strip zeros
of `L(·, χ)` with imaginary part in the window `(1, 2πe / q]`: a count leaf, at most one zero,
and a multiplicity leaf, every such zero simple. Both come from P0014 page 38 display 4.26 as
used in the band of P0014 Part IV page 431, read at a small conductor.

The source of both facts at a small conductor is a rigorous low zero table: Rumely,
Numerical computations concerning the ERH, Math. Comp. 61 1993, verifies GRH with all zeros
located for every primitive character of conductor at most `13` up to height `10000` and of
conductor at most `72` up to height `2500`; Platt, Numerical computations concerning the GRH,
Math. Comp. 85 2016, does the same for conductor at most `400000`. For every conductor here except `11`, the lowest
positive zero of every primitive character lies above `2πe / q`, so the window is empty.
Conductor `11` is the exception: one character has a zero at height `1.2311…`, see below. Session S125 rechecked this numerically by two independent methods, an argument
principle count of the completed `L`-function and sign changes of the Hardy function; see the
notes file `notes/burst-20261122/HelfgottMajor-SPLIT_book_count_band_above_one_mult_le-p2.md`.

So each conductor except `11` gets ONE zero free LEAF, and both the count leaf and the
multiplicity leaf of that conductor are proved from it here, with their exact statements, as
twins with the suffix `_s125`. For the 11 conductors this turns 22 HARD leaves into 11. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122BandZeroFree
open LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology

variable {q : ℕ} [NeZero q]

/-- An empty window gives the count bound: if no strip zero up to height `T` has imaginary
part above `1`, then the band filter is empty, so its card is at most one. Proved. -/
theorem band_card_le_one_of_window_free (χ : DirichletCharacter ℂ q) (T : ℝ)
    (h : ∀ ρ ∈ stripZeros χ T, ρ.im ≤ 1) :
    ((stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have hempty : (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
    apply Finset.filter_false_of_mem
    intro ρ hρ hc
    have := h ρ ((stripZeros_finite χ T).mem_toFinset.mp hρ)
    linarith [hc.2]
  rw [hempty]
  simp

/-- An empty window gives the multiplicity bound, vacuously. Proved. -/
theorem band_mult_le_one_of_window_free (χ : DirichletCharacter ℂ q) (T : ℝ)
    (h : ∀ ρ ∈ stripZeros χ T, ρ.im ≤ 1) :
    ∀ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im),
      (mult χ ρ : ℝ) ≤ 1 := by
  intro ρ hρ
  have hp := Finset.mem_filter.mp hρ
  have := h ρ ((stripZeros_finite χ T).mem_toFinset.mp hp.1)
  exact absurd hp.2.2 (not_lt.mpr this)

/-! ## Conductor `3`, window `(1, 2πe / 3]`, height below `5.70` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 3`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `3`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 3]`. The window height `2πe / 3` is below `5.70`.
Session S125 found the window empty for every primitive character of conductor `3` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_three (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 3) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `Feed1122BandAboveOne.band_above_one_card_level_three`, same statement, from the zero free LEAF of conductor `3`. -/
theorem band_above_one_card_level_three_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 3) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_three χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_three`, same statement, from the
zero free LEAF of conductor `3`. -/
theorem band_above_one_mult_level_three_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 3) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_three χ hχ hq)

/-! ## Conductor `4`, window `(1, 2πe / 4]`, height below `4.27` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 4`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `4`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 4]`. The window height `2πe / 4` is below `4.27`.
Session S125 found the window empty for every primitive character of conductor `4` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_four (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 4) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `Feed1122BandAboveOne.band_above_one_card_level_four`, same statement, from the zero free LEAF of conductor `4`. -/
theorem band_above_one_card_level_four_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 4) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_four χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_four`, same statement, from the
zero free LEAF of conductor `4`. -/
theorem band_above_one_mult_level_four_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 4) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_four χ hχ hq)

/-! ## Conductor `5`, window `(1, 2πe / 5]`, height below `3.42` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 5`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `5`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 5]`. The window height `2πe / 5` is below `3.42`.
Session S125 found the window empty for every primitive character of conductor `5` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_five (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 5) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `Feed1122BandAboveOne.band_above_one_card_level_five`, same statement, from the zero free LEAF of conductor `5`. -/
theorem band_above_one_card_level_five_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 5) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_five χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_five`, same statement, from the
zero free LEAF of conductor `5`. -/
theorem band_above_one_mult_level_five_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 5) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_five χ hχ hq)

/-! ## Conductor `7`, window `(1, 2πe / 7]`, height below `2.44` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 7`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `7`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 7]`. The window height `2πe / 7` is below `2.44`.
Session S125 found the window empty for every primitive character of conductor `7` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_seven (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 7) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `Feed1122BandAboveOne.band_above_one_card_level_seven`, same statement, from the zero free LEAF of conductor `7`. -/
theorem band_above_one_card_level_seven_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 7) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_seven χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_seven`, same statement, from the
zero free LEAF of conductor `7`. -/
theorem band_above_one_mult_level_seven_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 7) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_seven χ hχ hq)

/-! ## Conductor `8`, window `(1, 2πe / 8]`, height below `2.14` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 8`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `8`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 8]`. The window height `2πe / 8` is below `2.14`.
Session S125 found the window empty for every primitive character of conductor `8` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_eight (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 8) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `Feed1122BandAboveOne.band_above_one_card_level_eight`, same statement, from the zero free LEAF of conductor `8`. -/
theorem band_above_one_card_level_eight_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 8) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_eight χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_eight`, same statement, from the
zero free LEAF of conductor `8`. -/
theorem band_above_one_mult_level_eight_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 8) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_eight χ hχ hq)

/-! ## Conductor `9`, window `(1, 2πe / 9]`, height below `1.90` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 9`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `9`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 9]`. The window height `2πe / 9` is below `1.90`.
Session S125 found the window empty for every primitive character of conductor `9` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_nine (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 9) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `Feed1122BandAboveOne.band_above_one_card_level_nine`, same statement, from the zero free LEAF of conductor `9`. -/
theorem band_above_one_card_level_nine_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 9) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_nine χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_nine`, same statement, from the
zero free LEAF of conductor `9`. -/
theorem band_above_one_mult_level_nine_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 9) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_nine χ hχ hq)

/-! ## Conductor `11`: NOT zero free, no LEAF here

Session S125 found a zero of the open strip in the window `(1, 2πe / 11]` for the odd primitive
character of modulus `11` of order `10` with `χ(2) = exp(-3πi/5)`: `L(1/2 + iγ, χ) = 0` with
`γ = 1.2311882409…`, inside `(1, 1.5527]`. So no zero free statement is made for conductor `11`;
its count leaf and multiplicity leaf in `Feed1122BandAboveOne.lean` stay as they are, both
consistent with this one simple zero. -/

/-! ## Conductor `12`, window `(1, 2πe / 12]`, height below `1.43` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 12`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `12`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 12]`. The window height `2πe / 12` is below `1.43`.
Session S125 found the window empty for every primitive character of conductor `12` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_twelve (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 12) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `Feed1122BandAboveOne.band_above_one_card_level_twelve`, same statement, from the zero free LEAF of conductor `12`. -/
theorem band_above_one_card_level_twelve_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 12) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_twelve χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_twelve`, same statement, from the
zero free LEAF of conductor `12`. -/
theorem band_above_one_mult_level_twelve_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 12) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_twelve χ hχ hq)

/-! ## Conductor `13`, window `(1, 2πe / 13]`, height below `1.32` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 13`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `13`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 13]`. The window height `2πe / 13` is below `1.32`.
Session S125 found the window empty for every primitive character of conductor `13` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_thirteen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 13) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `ZeroCount1623.book_count_band_above_one_mult_le_card_level_thirteen_F1607`, same statement, from the zero free LEAF of conductor `13`. -/
theorem band_above_one_card_level_thirteen_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 13) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_thirteen χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_thirteen`, same statement, from the
zero free LEAF of conductor `13`. -/
theorem band_above_one_mult_level_thirteen_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 13) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_thirteen χ hχ hq)

/-! ## Conductor `15`, window `(1, 2πe / 15]`, height below `1.14` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 15`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `15`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 15]`. The window height `2πe / 15` is below `1.14`.
Session S125 found the window empty for every primitive character of conductor `15` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_fifteen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 15) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `ZeroCount1623.book_count_band_above_one_mult_le_card_level_fifteen_F1607`, same statement, from the zero free LEAF of conductor `15`. -/
theorem band_above_one_card_level_fifteen_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 15) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_fifteen χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_fifteen`, same statement, from the
zero free LEAF of conductor `15`. -/
theorem band_above_one_mult_level_fifteen_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 15) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_fifteen χ hχ hq)

/-! ## Conductor `16`, window `(1, 2πe / 16]`, height below `1.07` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 16`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `16`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 16]`. The window height `2πe / 16` is below `1.07`.
Session S125 found the window empty for every primitive character of conductor `16` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_sixteen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 16) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `ZeroCount1623.book_count_band_above_one_mult_le_card_level_sixteen_F1607`, same statement, from the zero free LEAF of conductor `16`. -/
theorem band_above_one_card_level_sixteen_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 16) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_sixteen χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_sixteen`, same statement, from the
zero free LEAF of conductor `16`. -/
theorem band_above_one_mult_level_sixteen_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 16) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_sixteen χ hχ hq)

/-! ## Conductor `17`, window `(1, 2πe / 17]`, height below `1.01` -/

/-- LEAF: P0014 page 38 display 4.26 at `q = 17`, the low zero table behind the band of
P0014 Part IV page 431, Rumely 1993 and Platt 2016. HARD.
For a primitive character of modulus exactly `17`, `L(·, χ)` has no zero of the open strip
with imaginary part in `(1, 2πe / 17]`. The window height `2πe / 17` is below `1.01`.
Session S125 found the window empty for every primitive character of conductor `17` by an
argument principle count and by sign changes of the Hardy function. -/
theorem band_window_zero_free_level_seventeen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 17) :
    ∀ ρ ∈ stripZeros χ (2 * Real.pi * Real.exp 1 / (q : ℝ)), ρ.im ≤ 1 := by
  sorry

/-- Twin of `ZeroCount1623.book_count_band_above_one_mult_le_card_level_seventeen_F1607`, same statement, from the zero free LEAF of conductor `17`. -/
theorem band_above_one_card_level_seventeen_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 17) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 :=
  band_card_le_one_of_window_free χ _ (band_window_zero_free_level_seventeen χ hχ hq)

/-- Twin of `Feed1122BandAboveOne.band_above_one_mult_level_seventeen`, same statement, from the
zero free LEAF of conductor `17`. -/
theorem band_above_one_mult_level_seventeen_s125 (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 17) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 :=
  band_mult_le_one_of_window_free χ _ (band_window_zero_free_level_seventeen χ hχ hq)

end LeanLab.HelfgottMajor.Feed1122BandZeroFree
