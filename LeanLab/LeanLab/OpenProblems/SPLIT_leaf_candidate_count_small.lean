import Mathlib

/-!
# SPLIT of `leaf_candidate_count_small`, folder OpenProblems, module SPLIT_leaf_card_lt_of_lcm_lt

AI wrote this Lean code. Goldbach is OPEN and Erdős Problem 273 is OPEN; nothing here claims
progress on either.

Target, unchanged and not restated in its own file: a finite set `T` of numbers `p - 1`, `p ≥ 5`
prime, all dividing a nonzero `L < 1965600`, has fewer than `100` members.

This is a pure counting statement about divisors. A lab count, Python over every `L` below the
bound, gives the maximum `99`, reached at `L = 1663200`, and `100` first at `L = 1965600`, so the
bound is sharp. The split cuts the range of `L` into four bands:

* `L < 8000` is proved here outright: at most `19` members exceed `L / 20`, since such a member is
  `L / j` with `j < 20`, and the members at most `L / 20` are below `400`, where only `76` numbers
  `d ≥ 4` have `d + 1` prime;
* the bands `[8000, 100000)`, `[100000, 1000000)` and `[1000000, 1965600)` are LEAFs: each is the
  same counting claim restricted to the band, a finite divisor count over the band.

`leaf_candidate_count_small_split` proves the target statement from the four bands with no `sorry`.
-/

namespace LeanLab.OpenProblems.Novelty1615

/-- The number of `d < 400` with `d ≥ 4` and `d + 1` prime: the primes `5 ≤ p ≤ 397`, that is
`78 - 2 = 76`. -/
private theorem card_small_candidates :
    ((Finset.range 400).filter (fun d => 4 ≤ d ∧ (d + 1).Prime)).card = 76 := by
  decide +kernel

/-- The low band, proved: for `0 < L < 8000` the count is at most `19 + 76 = 95`. -/
theorem candidate_count_band_low (L : ℕ) (hL0 : 0 < L) (hL : L < 8000) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (p := fun d => L < 20 * d)
  have h1 : (T.filter fun d => L < 20 * d).card ≤ 19 := by
    have hinj : Set.InjOn (fun d => L / d) ((T.filter fun d => L < 20 * d) : Set ℕ) := by
      intro a ha b hb hab
      have ha' := hdvd a (Finset.mem_filter.mp ha).1
      have hb' := hdvd b (Finset.mem_filter.mp hb).1
      simp only at hab
      rw [← Nat.div_div_self ha' hL0.ne', ← Nat.div_div_self hb' hL0.ne', hab]
    have hsub : (T.filter fun d => L < 20 * d).image (fun d => L / d) ⊆ Finset.Ioo 0 20 := by
      intro j hj
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hdT, hlt⟩ := Finset.mem_filter.mp hd
      have hdL : d ∣ L := hdvd d hdT
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdL hL0
      have hdle : d ≤ L := Nat.le_of_dvd hL0 hdL
      rw [Finset.mem_Ioo]
      refine ⟨Nat.div_pos hdle hdpos, ?_⟩
      rw [Nat.div_lt_iff_lt_mul hdpos]
      linarith
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj] at this
    simpa using this
  have h2 : (T.filter fun d => ¬ L < 20 * d).card ≤ 76 := by
    rw [← card_small_candidates]
    apply Finset.card_le_card
    intro d hd
    obtain ⟨hdT, hle⟩ := Finset.mem_filter.mp hd
    obtain ⟨p, hp, h5, rfl⟩ := hform d hdT
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, ?_⟩
    rwa [Nat.sub_add_cancel (by omega)]
  omega

/-- LEAF: counting step of `leaf_candidate_count_small` on the band `8000 ≤ L < 100000`. A finite
set of numbers `p - 1`, `p ≥ 5` prime, all dividing such an `L`, has fewer than `100` members. Class
MEDIUM: the same divisor count as the target restricted to this band; the lab count gives a maximum
well below `100` here, and a sharper cut at `L / k` than the one in `candidate_count_band_low`
together with the even shape of the members is the expected route. -/
theorem leaf_candidate_count_band_8000 (L : ℕ) (hL1 : 8000 ≤ L) (hL : L < 100000) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  sorry

/-- LEAF: counting step of `leaf_candidate_count_small` on the band `100000 ≤ L < 1000000`. A finite
set of numbers `p - 1`, `p ≥ 5` prime, all dividing such an `L`, has fewer than `100` members. Class
HARD: a finite divisor count over the band, by the factorization of `L` and the exponent cases as in
the reciprocal-test helpers of `SPLIT_leaf_card_lt_of_lcm_lt`, for the `L` with many even divisors. -/
theorem leaf_candidate_count_band_1e5 (L : ℕ) (hL1 : 100000 ≤ L) (hL : L < 1000000) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  sorry

/-- LEAF: counting step of `leaf_candidate_count_small` on the top band `1000000 ≤ L < 1965600`. A
finite set of numbers `p - 1`, `p ≥ 5` prime, all dividing such an `L`, has fewer than `100` members.
Class HARD: this band holds the sharp case, `L = 1663200` with `99` such divisors by the lab count,
so no slack is left and the count must be exact on the `L` with many even divisors. -/
theorem leaf_candidate_count_band_1e6 (L : ℕ) (hL1 : 1000000 ≤ L) (hL : L < 1965600) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  sorry

/-- The statement of `leaf_candidate_count_small`, assembled from the four bands with no `sorry`. -/
theorem leaf_candidate_count_small_split (L : ℕ) (hL0 : 0 < L) (hL : L < 1965600) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  by_cases h1 : L < 8000
  · exact candidate_count_band_low L hL0 h1 T hdvd hform
  by_cases h2 : L < 100000
  · exact leaf_candidate_count_band_8000 L (by omega) h2 T hdvd hform
  by_cases h3 : L < 1000000
  · exact leaf_candidate_count_band_1e5 L (by omega) h3 T hdvd hform
  · exact leaf_candidate_count_band_1e6 L (by omega) hL T hdvd hform

end LeanLab.OpenProblems.Novelty1615

#print axioms LeanLab.OpenProblems.Novelty1615.candidate_count_band_low
#print axioms LeanLab.OpenProblems.Novelty1615.leaf_candidate_count_small_split
