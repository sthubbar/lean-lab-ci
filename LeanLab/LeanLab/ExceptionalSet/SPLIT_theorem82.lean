/-
Split of `theorem82` of `LeanLab.ExceptionalSet.BhowmikGrimmelt2026` into two leaves.

`theorem82` says: for `δ ∈ (0, 1)` there is `c > 0` such that for every `A > 5/2`, every large
`r` and `X = r^A`, the almost-all multiples hypothesis `HL84 r δ X` rules out a real zero
`β > 1 - c / log X` of a primitive real character modulo `r`. The page-32 argument of the module
has two deferred steps; everything else it needs is already proved there (`dichotomy`,
`exists_good_multiple`, `Sing_pos`, `sq_eq_one_of_dirichlet_neg_one`, and the assembly
`theorem82_of_prop81`, all proved there with no open input):

* LEAF 1, the analytic step: at such a zero, `r₂(N)` has the shape `(1 + χ(-1) b) 𝔖(N) N + E`
  with `|b - 1| < 3δ/4` and `|E| ≤ (δ/4) 𝔖(N) N`, for every even multiple `N` of `r` in `[X/2, X]`
  outside an exceptional set `B` of at most `X^{3/5}` values.
* LEAF 2, the counting step: for `A > 5/2` and `r` large the even multiples of `r` in `[X/2, X]`
  outnumber `2 X^{3/5}`, so `B` and the `X^{3/5}` lost values still leave a multiple behind.

`theorem82_split` is the statement of `theorem82`, character for character, assembled from those
two leaves with no `sorry` and without `theorem82`. Each leaf is strictly easier than the whole:
the first drops the pigeonhole and the negation of the zero, the second drops all analysis. Both
leaves are OPEN; the assembly compiles with them open.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.BhowmikGrimmelt2026

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction

noncomputable section

/-- LEAF 1 of 2, the analytic step. Let `δ ∈ (0, 1)`, let `χ` be a primitive real character
modulo `r` with a real zero `β ∈ (1 - c / log X, 1)`, and let `X = r ^ A` with `A > 5/2`. Then
there is a set `B` of at most `X^{3/5}` values such that at every even multiple `N` of `r` in
`[X/2, X]` outside `B` the sum `r₂(N) = ∑_{n₁+n₂=N} Λ n₁ Λ n₂` equals
`(1 + χ(-1) b) 𝔖(N) N + E` with a shift `|b - 1| < 3δ/4` and an error `|E| ≤ (δ/4) 𝔖(N) N`.

The constant `1` in the bound on `B` normalises the size of the exceptional set; only that the
bound is a fixed multiple of `X^{3/5}` matters below, and the count in LEAF 2 absorbs twice it.
Nothing is asserted about the zero, about `HL84`, or about `N` inside `B`. -/
theorem leaf_expansion_off_exceptional_set :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 5 / 2 < A → ∃ r0 : ℕ,
      ∀ (r : ℕ) [NeZero r], r0 ≤ r → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
        (∀ a, (χ a).im = 0) →
        (∃ β : ℝ, 1 - c / Real.log ((r : ℝ) ^ A) < β ∧ β < 1 ∧
          DirichletCharacter.LFunction χ β = 0) →
        ∃ B : Finset ℕ, (B.card : ℝ) ≤ ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) ∧
          ∀ N ∈ evenMult r ((r : ℝ) ^ A), N ∉ B → ∃ b E : ℝ, |b - 1| < 3 * δ / 4 ∧
            |E| ≤ δ / 4 * (Sing N * N) ∧
            r2 N = (1 + (χ (-1)).re * b) * (Sing N * N) + E := by
  sorry

/-- LEAF 2 of 2, the counting step: for `X = r ^ A` with `A > 5/2` and `r` large, the even
multiples of `r` in `[X/2, X]` outnumber `2 X^{3/5}`.

This is where the exponent threshold `5/2` comes from: the count grows like `X / r = r^{A-1}`,
while `X^{3/5} = r^{3A/5}`, and `A - 1 > 3A/5` exactly when `A > 5/2`, so the ratio tends to
infinity in `r` for each fixed `A > 5/2`. The order of the quantifiers is the statement's own:
`r0` comes after `A` and does depend on it. A single `r0` for all `A > 5/2` does not exist, since
at `A = 5/2 + ε` the inequality needs `r^{2ε/5} > 4`, so `r0 → ∞` as `ε → 0`. No analysis is
asserted here. -/
theorem leaf_even_multiples_dominate_exceptions :
    ∀ A : ℝ, 5 / 2 < A → ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
      2 * (((r : ℝ) ^ A) ^ (3 / 5 : ℝ)) < ((evenMult r ((r : ℝ) ^ A)).card : ℝ) := by
  sorry

/-- `theorem82` of `LeanLab.ExceptionalSet.BhowmikGrimmelt2026`, assembled from the two leaves:
the exceptional set of LEAF 1 and the two extra multiples of LEAF 2 leave an even multiple `N` of
`r` in `[X/2, X]` outside `B` at which `HL84` holds, and `dichotomy` refutes `HL84` there for the
sign `χ(-1) = ±1`. -/
theorem theorem82_split : Theorem82 := by
  have h81 : Prop81AtMultiples := by
    intro δ hδ hδ1
    obtain ⟨c, hc, hstep⟩ := leaf_expansion_off_exceptional_set δ hδ hδ1
    refine ⟨c, hc, fun A hA => ?_⟩
    obtain ⟨ra, hra⟩ := hstep A hA
    obtain ⟨rc, hrc⟩ := leaf_even_multiples_dominate_exceptions A hA
    refine ⟨max ra rc, fun r _ hr χ hprim hreal hzero => ?_⟩
    have hra' : ra ≤ r := le_trans (le_max_left _ _) hr
    have hrc' : rc ≤ r := le_trans (le_max_right _ _) hr
    obtain ⟨B, hBcard, hBN⟩ := hra r hra' χ hprim hreal hzero
    have hcount : 2 * (((r : ℝ) ^ A) ^ (3 / 5 : ℝ)) < ((evenMult r ((r : ℝ) ^ A)).card : ℝ) :=
      hrc r hrc'
    refine ⟨B, by linarith, fun N hN hNB => hBN N hN hNB⟩
  exact theorem82_of_prop81 h81

-- Axiom audit driver for the assembly.
#print axioms theorem82_split

end

end LeanLab.ExceptionalSet.BG2026
