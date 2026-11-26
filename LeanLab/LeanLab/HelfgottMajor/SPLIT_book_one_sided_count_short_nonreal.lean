import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_short_conductor_le_height

/-!
# Split of `book_one_sided_count_short_nonreal`

The one sided count of book display 3.95 for a non real primitive character on `2 ≤ T ≤ 20`. The
source of 3.95 is the book draft Part I, chapter 3, section 3.7.3.3, page 86, with its footnote 5:
Trudgian, Math. Comp. 84 2015, Theorem 1, bounds the sum of the counts of `χ` and of its
conjugate, and the book says a look at Trudgian's section 2 gives the one sided bound with half
the constants, at `η = 0.20` of his Table 1.

This file splits by the size of the analytic conductor `qT`:

* small range, `qT ≤ 24`, proved from the Bennett et al. two sided leaf
  `bennett_two_sided_zero_count`: there the whole two sided count already fits under the one
  sided main term plus `3.389`: the second copy of the main term is at most `0.79`, because
  `T ≤ 12` and `log (qT/(2πe)) ≤ 0.41`, and
  `ℓ = log (q (T + 2)/(2π)) ≤ 2.1`;
* LEAF, the remaining range `24 < qT`, the book display 3.95 there.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The one sided book count is at most the two sided closed count. From
`bookCount_add_inv_le` and the nonnegativity of the count of `χ⁻¹`, no input. -/
lemma bookCount_le_two_sided (χ : DirichletCharacter ℂ q) (T : ℝ) :
    bookCount χ T ≤ ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) := by
  have h1 := bookCount_add_inv_le χ T
  have h2 := bookCount_nonneg' χ⁻¹ T
  linarith

/-- The arithmetic of the small range: for `qT ≤ 24`, `q ≥ 2`, `2 ≤ T`, `2πe ≤ qT` and
`ℓ ≤ 2.1`, the two sided main term plus `1/4` plus the Bennett error is at most the one sided
main term plus the book error. Proved, no input. -/
lemma small_conductor_two_sided_fits {T : ℝ} (hq2 : 2 ≤ q) (hT2 : 2 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) (hsmall : (q : ℝ) * T ≤ 24)
    (hℓ0 : 0 ≤ Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)))
    (hℓ : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 2.1) :
    T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) + 1 / 4 +
        (0.22737 * Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) +
          2 * Real.log (1 + Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi))) - 0.5) ≤
      bookMain q T + bookError q T := by
  have hq2r : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hpi3 := Real.pi_gt_d2
  have hpi0 := Real.pi_pos
  have he := Real.exp_one_gt_d9
  have hpe : (17.07 : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by nlinarith
  have hpe0 : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  set ℓ := Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) with hℓdef
  set Lg := Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) with hLgdef
  have hT12 : T ≤ 12 := by nlinarith
  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hLg0 : 0 ≤ Lg := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hpe0]; linarith
  have hLg1 : Lg ≤ 0.41 := by
    have hpos : 0 < (q : ℝ) * T / (2 * Real.pi * Real.exp 1) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have h2 : (q : ℝ) * T / (2 * Real.pi * Real.exp 1) ≤ 24 / 17.07 := by
      rw [div_le_div_iff₀ hpe0 (by norm_num)]
      nlinarith
    linarith [show (24 : ℝ) / 17.07 - 1 ≤ 0.41 by norm_num]
  have hlog1 : Real.log (1 + ℓ) ≤ 1.15 := by
    have hpos : 0 < 1 + ℓ := by linarith
    rw [Real.log_le_iff_le_exp hpos]
    have h1 : Real.exp 1.15 = Real.exp 1 * Real.exp 0.15 := by
      rw [← Real.exp_add]; norm_num
    have h2 : (1.15 : ℝ) ≤ Real.exp 0.15 := by
      have := Real.add_one_le_exp (0.15 : ℝ); linarith
    rw [h1]
    nlinarith
  have hlogq : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg hqT1
  have hM : T / Real.pi * Lg ≤ 12 / 3.14 * 0.41 := by
    have h1 : T / Real.pi ≤ 12 / 3.14 := by
      rw [div_le_div_iff₀ hpi0 (by norm_num)]; nlinarith
    exact mul_le_mul h1 hLg1 hLg0 (by norm_num)
  have hMeq : T / Real.pi * Lg = 2 * bookMain q T := by
    unfold bookMain; rw [← hLgdef]; ring
  have hbm : 0 ≤ bookMain q T := bookMain_nonneg' hmain
  unfold bookError
  have hfin : (12 : ℝ) / 3.14 * 0.41 / 2 + 1 / 4 + (0.22737 * 2.1 + 2 * 1.15 - 0.5) ≤ 3.389 := by
    norm_num
  nlinarith

/-- For `qT ≤ 24` and `T ≥ 2` the parameter `ℓ = log (q (T + 2)/(2π))` is at most `2.1`, since
`q (T + 2) ≤ qT + qT = 48 ≤ 2π e^{2.1}`. Proved, no input. -/
lemma ell_le_of_small_conductor {T : ℝ} (hT2 : 2 ≤ T) (hsmall : (q : ℝ) * T ≤ 24) :
    Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 2.1 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpi3 := Real.pi_gt_d2
  have hpi0 := Real.pi_pos
  have hpos : 0 < (q : ℝ) * (T + 2) / (2 * Real.pi) := by
    apply div_pos _ (by positivity)
    exact mul_pos (by linarith) (by linarith)
  rw [Real.log_le_iff_le_exp hpos]
  have he := Real.exp_one_gt_d9
  have h1 : Real.exp 2.1 = Real.exp 1 * Real.exp 1 * Real.exp 0.1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h2 : (1.1 : ℝ) ≤ Real.exp 0.1 := by
    have := Real.add_one_le_exp (0.1 : ℝ); linarith
  have h3 : (8.1 : ℝ) ≤ Real.exp 2.1 := by
    rw [h1]
    have : (7.38 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The small conductor range `qT ≤ 24` of the one sided count, for any primitive character of
modulus `q ≥ 2`. Proved from the Bennett et al. leaf `bennett_two_sided_zero_count`, so
CONDITIONAL ON that leaf. -/
theorem book_one_sided_count_small_conductor (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq2 : 2 ≤ q) {T : ℝ} (hT2 : 2 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) (hsmall : (q : ℝ) * T ≤ 24) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  have hN := bookCount_le_two_sided χ T
  have hB := bennett_two_sided_zero_count χ hχ (by omega) (by linarith : (5 : ℝ) / 7 ≤ T)
  have hbm : 0 ≤ bookMain q T := bookMain_nonneg' hmain
  have hq2r : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlogq : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  by_cases hℓ : Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) ≤ 1.567
  · have h0 := hB.1 hℓ
    unfold bookError
    linarith
  · have hgt : 1.567 < Real.log ((q : ℝ) * (T + 2) / (2 * Real.pi)) := not_le.mp hℓ
    have hab := (abs_le.mp (hB.2 hgt)).2
    have hre : -1 ≤ (χ (-1)).re := by
      have h1 := Complex.abs_re_le_norm (χ (-1))
      have h2 := DirichletCharacter.norm_le_one χ (-1)
      have h3 := neg_abs_le (χ (-1)).re
      linarith
    have hfit := small_conductor_two_sided_fits hq2 hT2 hmain hsmall (by linarith)
      (ell_le_of_small_conductor hT2 hsmall)
    linarith

/-- LEAF: the one sided zero count for a non real primitive character on `2 ≤ T ≤ 20` with
`qT > 24`. HARD, CITED. Helfgott, The ternary Goldbach problem, book draft Part I, chapter 3,
section 3.7.3.3, display 3.95, page 86, with footnote 5: from Trudgian, Math. Comp. 84 2015,
Theorem 1 and section 2 at `η = 0.20`, the zeros of `L(s, χ)` with `0 ≤ γ ≤ T`, half weight at the
ends, number at most `T/(2π) log (qT/(2πe)) + 0.15 log (qT) + 3.389`; used in Part IV, chapter 16,
proof of Lemma 16.9, page 431, error display 16.21. -/
theorem book_one_sided_count_short_nonreal_large (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hcx : χ⁻¹ ≠ χ) (hq2 : 2 ≤ q) {T : ℝ} (hT2 : 2 ≤ T) (hT20 : T ≤ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) (hlarge : 24 < (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Split of `book_one_sided_count_short_nonreal`, same statement: the small conductor range from
Bennett et al., the rest from the display 3.95 leaf. -/
theorem book_one_sided_count_short_nonreal_split (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hcx : χ⁻¹ ≠ χ) (hq2 : 2 ≤ q) {T : ℝ} (hT2 : 2 ≤ T) (hT20 : T ≤ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  by_cases hsmall : (q : ℝ) * T ≤ 24
  · exact book_one_sided_count_small_conductor χ hχ hq2 hT2 hmain hsmall
  · exact book_one_sided_count_short_nonreal_large χ hχ hcx hq2 hT2 hT20 hmain
      (not_le.mp hsmall)

end LeanLab.HelfgottMajor.ZeroCount1623
