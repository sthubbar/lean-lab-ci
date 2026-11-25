import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le
import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_one_level_le_six
import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_one_level_one
import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_one_level_le_twelve
import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_one_level_le_seventeen

/-!
# Split of `book_count_band_above_one_mult_le_one`

`book_count_band_above_one_mult_le_one` says that on the band `1 ≤ T`,
`q * T ≤ 2 * π * e` every strip zero of `L(·, χ)` whose imaginary part lies in the half
open window `(1, T]` has multiplicity at most one. It is the pointwise half of the
parent count: one zero at a time, with no statement about how many zeros the window holds.

The multiplicity of a zero is a local quantity, and it can only exceed one where the
`L`-function has a repeated zero. Nothing in the argument is a relaxation of the
multiplicity bound itself, which is a natural number compared with `1`; what the band
supplies instead is a hard ceiling on the height and on the conductor at once:

* the band caps the height at `2πe / q`, and the window grows with the height, so a bound
  at the single top height `2πe / q` gives the bound at every `T` of the band. The
  monotone step is proved below, so the leaves below carry no `T` at all;
* with `1 ≤ T` the band also bounds the conductor by `2πe < 18`, so only the primitive
  characters of modulus at most `17` occur. The block `q = 1` is the one whose window
  reaches the whole interval `(1, 2πe]` and it is also the only block in which the window
  provably holds a zero at all, the fixed zero of the trivial-character-free case at height
  `14.1347…`; the three remaining blocks cover the conductors `2` to `6`, `7` to `12` and
  `13` to `17`, whose windows are at most the short intervals `(1, 2πe / q]`.

Each leaf is therefore one instance of the claim, at one height and for one block of
conductors, and none of them quantifies over the band. The assembly is the case analysis
over the blocks together with the two proved arithmetic facts about the band.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The band caps the height at `2πe / q`, because `0 < q`. Proved, no input.

Degenerate cases: `q = 0` is excluded by `[NeZero q]`; the division is by a positive real
cast, so no Lean division by zero and no `Nat` division occurs. -/
private lemma one_split_band_top_ge {T : ℝ}
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
private lemma one_split_window_subset (χ : DirichletCharacter ℂ q) {T T' : ℝ} (h : T ≤ T') :
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
private lemma one_split_band_mod_le {T : ℝ} (hT : 1 ≤ T)
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
`1` every strip zero of `L(·, χ)` whose imaginary part lies in `(1, 2πe]` has multiplicity at
most one. This is the block whose window reaches the full band height and the only block in
which the window is known to hold a zero, the one at height `14.1347…`; the leaf asserts the
simplicity of such a zero and says nothing about how many zeros the window holds and nothing
about any conductor other than `1`. -/
theorem book_count_band_above_one_mult_le_one_level_one (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 1) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  exact book_count_band_above_one_mult_le_one_level_one_of_leaves χ hχ hq

/-- LEAF. Conductors `2` to `6`, at the top height of the band: for a primitive character of
modulus `q` in that range every strip zero of `L(·, χ)` whose imaginary part lies in
`(1, 2πe / q]` has multiplicity at most one. The band height is at most `πe` here, and the
window is the shortest that still begins above height `1`; the leaf asserts the simplicity of
the zeros that window holds, says nothing about `q = 1` or about the conductors above `6`, and
nothing about how many zeros the window holds. -/
theorem book_count_band_above_one_mult_le_one_level_le_six (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hq6 : q ≤ 6) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  exact book_count_band_above_one_mult_le_one_level_le_six_of_leaves χ hχ hq2 hq6

/-- LEAF. Conductors `7` to `12`, at the top height of the band: for a primitive character of
modulus `q` in that range every strip zero of `L(·, χ)` whose imaginary part lies in
`(1, 2πe / q]` has multiplicity at most one. The band height is at most `2πe / 7 < 1.6` here,
so the window is a short one just above height `1`; the leaf speaks only about this block of
conductors and only about multiplicity, not about the number of zeros in the window. -/
theorem book_count_band_above_one_mult_le_one_level_le_twelve (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hq12 : q ≤ 12) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  exact book_count_band_above_one_mult_le_one_level_le_twelve_of_leaves χ hχ hq7 hq12

/-- LEAF. Conductors `13` to `17`, at the top height of the band: for a primitive character of
modulus `q` in that range every strip zero of `L(·, χ)` whose imaginary part lies in
`(1, 2πe / q]` has multiplicity at most one. The band height is at most `2πe / 13 < 1.32`
here, the shortest window of the four blocks; since `q ≤ 17` exhausts the band this block
closes the case analysis, and the leaf asserts only the multiplicity bound. -/
theorem book_count_band_above_one_mult_le_one_level_le_seventeen (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq13 : 13 ≤ q) (hq17 : q ≤ 17) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  exact book_count_band_above_one_mult_le_one_level_le_seventeen_of_leaves χ hχ hq13 hq17

/-- Assembly: the pointwise multiplicity bound of the band follows from the four conductor
blocks and the two arithmetic facts about the band. The band caps the height at `2πe / q`, the
window is monotone in the height, so a zero of the window at `T` also lies in the window at the
top height, where the block that holds `q` bounds its multiplicity by one. -/
theorem book_count_band_above_one_mult_le_one_split (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im),
      (mult χ ρ : ℝ) ≤ 1 := by
  have htop : T ≤ 2 * Real.pi * Real.exp 1 / (q : ℝ) := one_split_band_top_ge hband
  have hq17 : q ≤ 17 := one_split_band_mod_le hT hband
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  intro ρ hρ
  have hmem : ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) := one_split_window_subset χ htop hρ
  rcases eq_or_ne q 1 with h1 | h1
  · have hqR : (q : ℝ) = 1 := by rw [h1]; norm_num
    have htop1 : 2 * Real.pi * Real.exp 1 / (q : ℝ) = 2 * Real.pi * Real.exp 1 := by
      rw [hqR, div_one]
    rw [htop1] at hmem
    exact book_count_band_above_one_mult_le_one_level_one χ hχ h1 ρ hmem
  · have h2 : 2 ≤ q := by omega
    by_cases h6 : q ≤ 6
    · exact book_count_band_above_one_mult_le_one_level_le_six χ hχ h2 h6 ρ hmem
    · have h7 : 7 ≤ q := by omega
      by_cases h12 : q ≤ 12
      · exact book_count_band_above_one_mult_le_one_level_le_twelve χ hχ h7 h12 ρ hmem
      · have h13 : 13 ≤ q := by omega
        exact book_count_band_above_one_mult_le_one_level_le_seventeen χ hχ h13 hq17 ρ hmem

#print axioms book_count_band_above_one_mult_le_one_split

end LeanLab.HelfgottMajor.ZeroCount1623
