import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le
import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_card_level_le_six
import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_card_level_le_twelve

/-!
# Split of `book_count_band_above_one_mult_le_card`

`book_count_band_above_one_mult_le_card` says that on the band `1 ≤ T`, `q * T ≤ 2πe`
the strip zeros of `L(·, χ)` whose imaginary part lies in `(1, T]` number at most one,
counted without multiplicity.

Two things are separated here, and neither is a cut of the numerical constant `1`, which
cannot be relaxed.

* The band ties the two parameters together: `T ≤ 2πe / q`, so the window at the height `T`
  sits inside the window at the single top height `2πe / q`, and the count at `T` is at most
  the count at that top height. This is the monotone half and it is proved below, so the
  leaves carry no `T` at all: each of them is one instance per `L`-function, at one height.
* The band also bounds the conductor, `q ≤ 2πe < 18` since `1 ≤ T`, so only the primitive
  characters with `q ≤ 17` occur. The counting input is a finite verification over those
  characters, and it is cut into four independent blocks: the conductor `1`, the conductors
  `2` to `6`, the conductors `7` to `12`, and the conductors `13` to `17`.

Each leaf is therefore one inequality about one height and one block of conductors, strictly
narrower than the parent statement, which quantifies over the whole band. The assembly is the
case analysis over the blocks together with the two proved arithmetic facts about the band.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The band caps the height at `2πe / q`, because `0 < q`. Proved, no input.

Degenerate cases: `q = 0` is excluded by `[NeZero q]`; the division is by a positive real
cast, so no Lean division by zero and no `Nat` division occurs. -/
private lemma card_split_band_top_ge {T : ℝ}
    (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    T ≤ 2 * Real.pi * Real.exp 1 / (q : ℝ) := by
  have hq : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [le_div_iff₀ hq]
  calc T * (q : ℝ) = (q : ℝ) * T := by ring
    _ ≤ 2 * Real.pi * Real.exp 1 := hband

/-- The window `1 < Im ρ` grows with the height: a strip zero of absolute imaginary part at
most `T` also has absolute imaginary part at most any `T' ≥ T`. Proved, no input.

Degenerate cases: at `T = T'` this is the identity; the empty set is contained in every set,
so the statement is not vacuous only when a zero exists, which is exactly what it is for. -/
private lemma card_split_window_subset (χ : DirichletCharacter ℂ q) {T T' : ℝ} (h : T ≤ T') :
    (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) ⊆
      (stripZeros_finite χ T').toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) := by
  intro ρ hρ
  have hp := Finset.mem_filter.mp hρ
  have hz := (stripZeros_finite χ T).mem_toFinset.mp hp.1
  exact Finset.mem_filter.mpr
    ⟨(stripZeros_finite χ T').mem_toFinset.mpr ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans h⟩, hp.2⟩

/-- The band bounds the conductor: `1 ≤ T` gives `q ≤ q * T ≤ 2πe < 18`, so `q ≤ 17`.
Proved from the two rational bounds on `π` and `exp 1`; no zero input.

Degenerate cases: `q = 1` is allowed, `q = 0` is excluded by `[NeZero q]`; `T` is real, so
no `Nat` subtraction or `Nat` division is involved. -/
private lemma card_split_band_mod_le {T : ℝ} (hT : 1 ≤ T)
    (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) : q ≤ 17 := by
  have hq : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1 : (q : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hpi := Real.pi_lt_d4
  have hexp := Real.exp_one_lt_d9
  have hpie : Real.pi * Real.exp 1 < 3.1416 * 2.7182818286 := by
    nlinarith [hpi, hexp, Real.pi_pos, Real.exp_pos 1]
  have h2 : (q : ℝ) < 18 := by nlinarith
  have h3 : q < 18 := by exact_mod_cast h2
  omega

/-- LEAF. Conductor one, at the top height of the band: for a primitive character of modulus
`1` the strip zeros of `L(·, χ)` whose imaginary part lies in `(1, 2πe]` number at most one,
counted without multiplicity. This is the only conductor for which the window is not empty
above height `1` up to the full band height, so it is the block that carries the explicit
zero of `ζ` at height `14.1347…`; nothing is asserted about any other conductor and nothing
about multiplicities. -/
theorem book_count_band_above_one_mult_le_card_level_one (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 1) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- LEAF. Conductors `2` to `6`, at the top height of the band: for a primitive character of
modulus `q` in that range the strip zeros of `L(·, χ)` with imaginary part in
`(1, 2πe / q]` number at most one, counted without multiplicity. The band height
`2πe / q` is at most `πe` here, so this block asks only that no two zeros of one such
`L`-function sit above height `1` below that fixed bound; multiplicities are not mentioned and
no statement is made about the conductors outside the block. -/
theorem book_count_band_above_one_mult_le_card_level_le_six (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hq6 : q ≤ 6) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  exact book_count_band_above_one_mult_le_card_level_le_six_of_leaves χ hχ hq2 hq6

/-- LEAF. Conductors `7` to `12`, at the top height of the band: for a primitive character of
modulus `q` in that range the strip zeros of `L(·, χ)` with imaginary part in
`(1, 2πe / q]` number at most one, counted without multiplicity. The band height is at most
`2πe / 7 < 1.6` here, so the window is a short one just above height `1`; the ζ-block and the
multiplicities are outside this leaf. -/
theorem book_count_band_above_one_mult_le_card_level_le_twelve (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hq12 : q ≤ 12) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  exact book_count_band_above_one_mult_le_card_level_le_twelve_of_leaves χ hχ hq7 hq12

/-- LEAF. Conductors `13` to `17`, at the top height of the band: for a primitive character of
modulus `q` in that range the strip zeros of `L(·, χ)` with imaginary part in
`(1, 2πe / q]` number at most one, counted without multiplicity. The band height is at most
`2πe / 13 < 1.32` here, so the window is the shortest of the four blocks; since `q ≤ 17`
covers the whole band this block is the last one, and multiplicities are outside it. -/
theorem book_count_band_above_one_mult_le_card_level_le_seventeen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq13 : 13 ≤ q) (hq17 : q ≤ 17) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- Assembly: the counting half of the band bound follows from the four conductor blocks and
the two arithmetic facts about the band. The band caps the height at `2πe / q`, the window is
monotone in the height, so the count at `T` is at most the count at the top height; the band
also bounds the conductor by `17`, and the four blocks cover `q = 1` and `2 ≤ q ≤ 6`,
`7 ≤ q ≤ 12`, `13 ≤ q ≤ 17`. -/
theorem book_count_band_above_one_mult_le_card_split (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ((stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  have htop : T ≤ 2 * Real.pi * Real.exp 1 / (q : ℝ) := card_split_band_top_ge hband
  have hmono : ((stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤
      ((stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
        (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card :=
    Finset.card_le_card (card_split_window_subset χ htop)
  have hq17 : q ≤ 17 := card_split_band_mod_le hT hband
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  rcases eq_or_ne q 1 with h1 | h1
  · have hqR : (q : ℝ) = 1 := by rw [h1]; norm_num
    have htop1 : 2 * Real.pi * Real.exp 1 / (q : ℝ) = 2 * Real.pi * Real.exp 1 := by
      rw [hqR, div_one]
    rw [htop1] at hmono
    exact hmono.trans (book_count_band_above_one_mult_le_card_level_one χ hχ h1)
  · have h2 : 2 ≤ q := by omega
    by_cases h6 : q ≤ 6
    · exact hmono.trans (book_count_band_above_one_mult_le_card_level_le_six χ hχ h2 h6)
    · have h7 : 7 ≤ q := by omega
      by_cases h12 : q ≤ 12
      · exact hmono.trans
          (book_count_band_above_one_mult_le_card_level_le_twelve χ hχ h7 h12)
      · have h13 : 13 ≤ q := by omega
        exact hmono.trans
          (book_count_band_above_one_mult_le_card_level_le_seventeen χ hχ h13 hq17)

#print axioms book_count_band_above_one_mult_le_card_split

end LeanLab.HelfgottMajor.ZeroCount1623
