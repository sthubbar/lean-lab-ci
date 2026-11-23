import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_short

/-!
# Split of `book_zero_count_large_height_upper_short_level_one`

Level one, `q = 1`. The `L`-function of the unique character mod `1` is the Riemann zeta function,
Mathlib `DirichletCharacter.LFunction_modOne_eq`. On `T ≤ 20` the count `bookCount χ T` is at most
the full multiplicity sum of the zeros of zeta with `0 < Re < 1` and `0 ≤ Im ≤ 20`, since every
half weight is at most `1`. The only input is the classical fact that this multiplicity sum is
`1`, the single simple zero `1/2 + 14.134725...i`: Backlund, Acta Math. 41 1918, the footnote on
the last page, which states that the 79 zeros he separated on the critical line with
`0 < t < 200` are the only zeros with imaginary part in that range; the first of them lies at
`14.134725`, Gram, Acta Math. 27 1903. The bound `3.389` then holds with room `2.389`.

The coordinator check: the Trudgian 2014 Corollary 1 bound at `T = 20` gives
`0.5026 + 0.875 + 0.3355 + 0.3051 + 2.510 + 0.01 = 4.54 > 3.389`, so that bound alone does NOT
give the leaf; the zero table is needed. The comment in the unit file that the count is at most
`0.5` is wrong: the count is exactly `1` for `14.1348 < T ≤ 20`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

/-- LEAF: the zeros of the Riemann zeta function below height 20. HARD, CITED. Backlund,
Über die Nullstellen der Riemannschen Zetafunktion, Acta Math. 41 1918, footnote on the last
page: the 79 zeros separated on the critical line with `0 < t < 200` are the only zeros with
imaginary part in `(0, 200)`; the least of them is `1/2 + 14.134725...i`, Gram, Acta Math. 27
1903, and the next is at height `21.022`. With zeta real and negative on `(0, 1)`, the sum of the
multiplicities of the zeros with `0 < Re < 1` and `0 ≤ Im ≤ 20` is exactly `1`; this leaf states
the upper half, for every finite set of such zeros. -/
theorem zeta_zero_mult_sum_height_twenty_le_one (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ 20) :
    ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
  sorry

/-- The book half weight is at most one. No input. -/
lemma halfWeight_le_one' (T γ : ℝ) : halfWeight T γ ≤ 1 := by
  unfold halfWeight; split_ifs <;> norm_num

/-- The book half weight is nonnegative. No input. -/
lemma halfWeight_nonneg' (T γ : ℝ) : 0 ≤ halfWeight T γ := by
  unfold halfWeight; split_ifs <;> norm_num

/-- The book count is at most the full multiplicity sum over the zeros with `0 ≤ Im ≤ T`.
No input. -/
lemma bookCount_le_upper_mult_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    bookCount χ T ≤ ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im),
      (mult χ ρ : ℝ) := by
  unfold bookCount
  apply Finset.sum_le_sum
  intro ρ _
  have hm : (0 : ℝ) ≤ (mult χ ρ : ℝ) := Nat.cast_nonneg _
  have := halfWeight_le_one' T ρ.im
  nlinarith

/-- Split of `book_zero_count_large_height_upper_short_level_one`, same statement, from the
zeta zero leaf and the identification of the modulus one `L`-function with zeta. -/
theorem book_zero_count_large_height_upper_short_level_one_split {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 1) {T : ℝ} (hT : 1 ≤ T) (hT20 : T ≤ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T ≤ 3.389 := by
  subst hq
  refine (bookCount_le_upper_mult_sum χ T).trans ?_
  have hL : DirichletCharacter.LFunction χ = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  have h := zeta_zero_mult_sum_height_twenty_le_one
    ((stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im)) (by
      intro ρ hρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
      obtain ⟨⟨h0, h1, h2, h3⟩, h4⟩ := hρ
      rw [hL] at h0
      exact ⟨h0, h1, h2, h4, (le_abs_self _).trans (h3.trans hT20)⟩)
  have he : ∀ ρ, (mult χ ρ : ℝ) = (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    intro ρ; simp only [mult, hL]
  simp only [he]
  linarith

end LeanLab.HelfgottMajor.ZeroCount1623
