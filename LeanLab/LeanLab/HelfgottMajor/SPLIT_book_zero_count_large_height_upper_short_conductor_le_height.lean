import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_short_level_one

/-!
# Split of `book_zero_count_large_height_upper_short_conductor_le_height`

The unit file cut the conductor range `q ≥ 2` into `q ≤ T` and `T < q`. Both pieces are the same
one sided count on `2 ≤ T ≤ 20`, so this file splits by a genuine mathematical distinction
instead, valid for both pieces at once, and the file for `T < q` reuses everything here.

* Bridging, proved: `bookCount χ T + bookCount χ⁻¹ T` is at most the two sided closed count
  `N(T, χ)`, the multiplicity sum over `stripZeros χ T`. This uses `bookCount_inv` of
  `ZeroCount1623`, the conjugate symmetry, and needs no gap condition, since the weights at a zero
  of height `0` add to exactly `1` and every other weight is at most `1`.
* LEAF, CITED: Bennett, Martin, O'Bryant and Rechnitzer, Math. Comp. 90 2021, Theorem 1.1, page
  1456, the explicit two sided count for a primitive character of conductor `q > 1`, `T ≥ 5/7`.
* Real characters, proved from the two items above: when `χ⁻¹ = χ` the two one sided counts are
  equal, so `2 bookCount χ T ≤ N(T, χ)`, and the Bennett error halved fits under the book error
  `0.15 log (qT) + 3.389` for every `q ≥ 2`, `T ≥ 2`, with no upper limit on `q`.
* LEAF, the remainder: the one sided count for a NON real primitive character, the book's own
  display 3.95 as used on page 431. A two sided count cannot give it, because it does not bound
  how the zeros split between `χ` and `χ⁻¹`: the bound `bookCount χ T ≤ N(T, χ)` loses a whole
  main term `T/(2π) log (qT/(2πe))`, up to `10.0` when `q ≤ T ≤ 20`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The book count is nonnegative. No input. -/
lemma bookCount_nonneg' (χ : DirichletCharacter ℂ q) (T : ℝ) : 0 ≤ bookCount χ T := by
  unfold bookCount
  exact Finset.sum_nonneg fun ρ _ =>
    mul_nonneg (halfWeight_nonneg' T ρ.im) (Nat.cast_nonneg _)

/-- The two one sided book counts of `χ` and `χ⁻¹` add up to at most the two sided closed
count. Proved from `bookCount_inv`, no gap condition, no input. -/
lemma bookCount_add_inv_le (χ : DirichletCharacter ℂ q) (T : ℝ) :
    bookCount χ T + bookCount χ⁻¹ T ≤
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) := by
  rw [bookCount_inv]
  unfold bookCount
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ρ _
  have hm : (0 : ℝ) ≤ (mult χ ρ : ℝ) := Nat.cast_nonneg _
  rcases lt_trichotomy ρ.im 0 with h | h | h
  · rw [if_neg (not_le.mpr h), if_pos h.le, zero_add]
    have := halfWeight_le_one' T (-ρ.im)
    nlinarith
  · rw [if_pos h.ge, if_pos h.le, h]
    simp only [halfWeight, neg_zero, true_or, if_true]
    linarith
  · rw [if_pos h.le, if_neg (not_le.mpr h), add_zero]
    have := halfWeight_le_one' T ρ.im
    nlinarith

/-- Dropping the nonnegative inverse count gives a one sided bound by the full strip count.
This does not halve a two sided estimate for a non real character. -/
lemma bookCount_le_stripCount' (χ : DirichletCharacter ℂ q) (T : ℝ) :
    bookCount χ T ≤
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) := by
  have hadd := bookCount_add_inv_le χ T
  have hnonneg := bookCount_nonneg' χ⁻¹ T
  exact le_of_add_le_of_nonneg_left hadd hnonneg

/-- The main term is nonnegative once `2πe ≤ qT`. No input. -/
lemma bookMain_nonneg' {T : ℝ} (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    0 ≤ bookMain q T := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpe : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  have hT0 : (0 : ℝ) < T := by nlinarith
  have hlog : 0 ≤ Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hpe]
    linarith
  unfold bookMain
  exact mul_nonneg (by positivity) hlog

/-- LEAF: the explicit two sided zero count for a primitive character. HARD, CITED. Bennett,
Martin, O'Bryant, Rechnitzer, Counting zeros of Dirichlet L-functions, Math. Comp. 90 2021,
Theorem 1.1, page 1456: for `χ` primitive of conductor `q > 1` and `T ≥ 5/7`, with
`ℓ = log (q (T + 2) / (2π))`, if `ℓ ≤ 1.567` then `N(T, χ) = 0`, and otherwise
`|N(T, χ) - (T/π log (qT/(2πe)) - χ(-1)/4)| ≤ 0.22737 ℓ + 2 log (1 + ℓ) - 0.5`. Here `N(T, χ)` is
the number of zeros with `0 < β < 1`, `|γ| ≤ T`, with multiplicity, which is the multiplicity sum
over the lab set `stripZeros χ T`; a primitive character mod `q` has conductor `q`, and
`χ(-1) = ±1` is real, so `χ(-1)` is written as its real part. -/
theorem bennett_two_sided_zero_count (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) {T : ℝ} (hT : 5 / 7 ≤ T) :
    (Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 1.567 →
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) = 0) ∧
    (1.567 < Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) →
      |∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) -
          (T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) -
            (χ (-1)).re / 4)| ≤
        0.22737 * Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) +
          2 * Real.log (1 + Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) - 0.5) := by
  sorry

/-- The arithmetic that the halved Bennett error fits under the book error, for `q ≥ 1`,
`T ≥ 2`, `qT ≥ 1` and `ℓ > 0`. Proved, no input. -/
lemma bennett_half_error_le_bookError {T : ℝ} (hT2 : 2 ≤ T) (hqT : 1 ≤ (q : ℝ) * T)
    (hℓ : 0 < Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) :
    (0.22737 * Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) +
        2 * Real.log (1 + Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) - 0.5 + 1 / 4) / 2 ≤
      bookError q T := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) with hℓdef
  set Lq := Real.log ((q : ℝ) * T) with hLqdef
  have hpi := Real.pi_gt_three
  have hLq0 : 0 ≤ Lq := Real.log_nonneg hqT
  have hpos : 0 < (q : ℝ) * (T + 2) / (2 * Real.pi) := by positivity
  have hle : (q : ℝ) * (T + 2) / (2 * Real.pi) ≤ (q : ℝ) * T := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hℓLqq : ℓ ≤ Lq := Real.log_le_log hpos hle
  have h1 : Real.log (1 + ℓ) ≤ Real.log (1 + Lq) := Real.log_le_log (by linarith) (by linarith)
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have h2 : Real.log (1 + Lq) ≤ 5 * Real.log 2 - 1 + (1 + Lq) / 32 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + Lq) / 32 by positivity)
    rw [Real.log_div (by positivity) (by norm_num), h32] at this
    linarith
  have hl2 := Real.log_two_lt_d9
  unfold bookError
  rw [← hLqdef]
  nlinarith

/-- Real characters, `χ⁻¹ = χ`: the book upper bound for every `q ≥ 2`, `T ≥ 2` with
`2πe ≤ qT`, proved from the Bennett et al. leaf and the conjugate symmetry. -/
theorem book_upper_short_real_character (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hreal : χ⁻¹ = χ) (hq2 : 2 ≤ q) {T : ℝ} (hT2 : 2 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  have hadd : bookCount χ T + bookCount χ T ≤
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) := by
    have := bookCount_add_inv_le χ T
    rwa [hreal] at this
  have hB := bennett_two_sided_zero_count χ hχ (by omega) (by linarith : (5 : ℝ) / 7 ≤ T)
  have hnn := bookMain_nonneg' (q := q) hmain
  have herr := bookError_ge_agy37 (q := q) (by linarith : (1 : ℝ) ≤ T)
  have hpe : (1 : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by
    have := Real.pi_gt_three
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  by_cases hℓ : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 1.567
  · have h0 := hB.1 hℓ
    linarith
  · have hgt : 1.567 < Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) := not_le.mp hℓ
    have hab := (abs_le.mp (hB.2 hgt)).2
    have hre : -1 ≤ (χ (-1)).re := by
      have h1 := Complex.abs_re_le_norm (χ (-1))
      have h2 := DirichletCharacter.norm_le_one χ (-1)
      have h3 := neg_abs_le (χ (-1)).re
      linarith
    have hmainEq : T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) =
        2 * bookMain q T := by
      unfold bookMain; ring
    have harith := bennett_half_error_le_bookError (q := q) hT2 (hpe.trans hmain)
      (by linarith)
    rw [hmainEq] at hab
    linarith

/-- LEAF: the one sided zero count for a non real primitive character on `2 ≤ T ≤ 20`. HARD,
CITED. Helfgott, The ternary Goldbach problem, Part IV, chapter 16, proof of Lemma 16.9, pages 431
and 432, with error display 16.21, citing display 3.95 of section 3.7.3.3, which is not in the
paper store: the zeros of `L(s, χ)` with `0 ≤ γ ≤ T`, half weight at the ends, number at most
`T/(2π) log (qT/(2πe)) + 0.15 log (qT) + 3.389`. It is left only for `χ⁻¹ ≠ χ`, since for real
characters the bound is proved above from Bennett et al. A two sided count does not imply it:
the zeros of height in `[0, T]` of `χ` and of `χ⁻¹` are not separated by it. -/
theorem book_one_sided_count_short_nonreal (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hcx : χ⁻¹ ≠ χ) (hq2 : 2 ≤ q) {T : ℝ} (hT2 : 2 ≤ T) (hT20 : T ≤ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Split of `book_zero_count_large_height_upper_short_conductor_le_height`, same statement:
real characters from Bennett et al. and the conjugate symmetry, non real characters from the one
sided leaf. -/
theorem book_zero_count_large_height_upper_short_conductor_le_height_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) {T : ℝ}
    (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  by_cases hreal : χ⁻¹ = χ
  · exact book_upper_short_real_character χ hχ hreal hq2 hT2 hmain
  · exact book_one_sided_count_short_nonreal χ hχ hreal hq2 hT2 hT20 hmain

end LeanLab.HelfgottMajor.ZeroCount1623

#print axioms LeanLab.HelfgottMajor.ZeroCount1623.bookCount_le_stripCount'
