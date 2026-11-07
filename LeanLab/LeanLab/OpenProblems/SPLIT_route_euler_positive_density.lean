import LeanLab.OpenProblems.State1612

/-!
# Split of `route_euler_positive_density` (OpenProblems, State1612)

The target asks for a positive density of those `n` whose `8n + 3` is an odd square plus twice a
prime: some `c > 0` with `c * X ≤ X - euExc X` for all large `X`.

Write `A X` for the set of `n` in `[1, X]` with `IsEuler (8n + 3)`, and `R n` for the number of
`k` with `4n + 1 - 2k(k+1)` prime, the multiplicity of the triangular form that the target's file
already records for this problem.  `R n` vanishes exactly at the values with no representation, so
the route is a first moment, a second moment and Cauchy-Schwarz:

  (sum of `R` over `A X`) ^ 2  <=  (#A X) * (sum of `R ^ 2` over `A X`),

and the two moments have sizes `X * sqrt X / log X` and `X ^ 2 / (log X) ^ 2`, whose ratio is
`X` up to the fixed constants.  This is where a positive density comes from, and it is why a
single crude pair count is not enough: a pair count alone only gives `X / log X` represented
values, because each value can carry up to `sqrt X` pairs.

1. `leaf_representation_multiplicity`: the multiplicity `R` exists, is the finite list count, and
   is nonzero exactly at the representable `n`.  This is the triangular form, a bookkeeping step.
2. `leaf_first_moment_card`: for such an `R` the total multiplicity over `A X` is at least
   `a * X * sqrt X / log X` with a fixed `a > 0`.  A prime count summed over `k <= sqrt X` gives
   this size.  Strictly weaker than the target: on its own it counts pairs, not represented values.
3. `leaf_second_moment_card`: for such an `R` the total of the squared multiplicity over `A X` is
   at most `b * X ^ 2 / (log X) ^ 2` with a fixed `b > 0`.  Strictly weaker than the target: a mean
   square bound says nothing about how many `n` are hit.
4. `leaf_cauchy_schwarz_density`: the two moment estimates and Cauchy-Schwarz give `c * X` as a
   lower bound for the cardinality of `A X`, with `c` the ratio of the squared first moment to the
   second moment.  Strictly weaker than the target: it bounds the size of `A X`, not `X - euExc X`.
5. `leaf_card_eq_complement`: the cardinality of `A X` is `X - euExc X`, the complement inside
   `[1, X]` of the exceptional set that the target's file counts.  An identity, with no estimate.

Every leaf is tested at the degenerate values.  At `X = 0` the interval `[1, 0]` is empty, both
finite sums are `0`, and both quotients are `0` by Lean's division convention (`Real.log 0 = 0`),
so the three inequalities hold there; each of them is an eventual statement, and the fifth is an
identity that also reads `0 = 0` at `X = 0`.  No leaf can fail at a small case, and no hypothesis
of leaf 2, 3 or 4 is unsatisfiable: leaf 1 produces an `R` meeting them, and at `X = 0` the
conclusion of leaf 4 reads `0 <= 0` rather than being vacuous.

No statement, import or definition of the target file is changed, and no definition, abbreviation,
structure, instance or notation is introduced here.
-/

namespace LeanLab.OpenProblems.State1612

open LeanLab
open scoped Classical

/-- LEAF 1, the multiplicity.  There is a multiplicity `R`, computed from the list form as the
number of `k` with `4n + 1 - 2k(k+1)` prime, and for `1 ≤ n` it is nonzero exactly where `8n + 3`
has an odd square plus twice a prime.  The bound `4n + 2` on `k` is safe: a term with
`2k(k+1) > 4n + 1` truncates to `0`, which is not prime, and every true solution has `k ≤ n`. -/
theorem leaf_representation_multiplicity :
    ∃ R : ℕ → ℕ,
      (∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
          (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card) ∧
      ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)) := by
  sorry

/-- LEAF 2, the first moment.  For a multiplicity `R` that is nonzero exactly on the representable
values, the total multiplicity over those `n ≤ X` is at least `a * X * sqrt X / log X` for a fixed
`a > 0`, for all large `X`.  For each `k` with `2k(k+1) ≤ X` the primes of the form
`4n + 1 - 2k(k+1)` are a fixed fraction of `X / log X`, and there are about `sqrt X` of those `k`;
the count here is over pairs, so it does not yet see how the pairs are spread over the values. -/
theorem leaf_first_moment_card (R : ℕ → ℕ)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ X : ℕ in Filter.atTop,
      a * (X : ℝ) * Real.sqrt (X : ℝ) / Real.log (X : ℝ) ≤
        Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ)) := by
  sorry

/-- LEAF 3, the second moment.  For a multiplicity `R` that is nonzero exactly on the representable
values, the total of the squared multiplicity over those `n ≤ X` is at most
`b * X ^ 2 / (log X) ^ 2` for a fixed `b > 0`, for all large `X`.  Two representations of the same
value differ by a difference of two primes equal to a difference of two squares, and the parallel
count of those differences on the scale `X` bounds the square sum.  A mean square bound is weaker
than a density statement: it does not say how many values carry a representation. -/
theorem leaf_second_moment_card (R : ℕ → ℕ)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) ^ 2)
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
  sorry

/-- LEAF 4, Cauchy-Schwarz.  Given a multiplicity `R` that is nonzero exactly on the representable
values, and the first and second moment estimates of LEAF 2 and LEAF 3 with constants `a` and `b`,
there is `c > 0` with `c * X ≤ #A X` for all large `X`.  On `A X` the multiplicity is at least
`1`, and Cauchy-Schwarz over `A X` gives `(sum R) ^ 2 ≤ (#A X) * (sum R ^ 2)`; dividing the
squared first moment by the second moment leaves `a ^ 2 / b` times `X`, since the two powers of the
logarithm cancel.  It bounds the number of representable values, and is weaker than the target,
which is about `X - euExc X`. -/
theorem leaf_cauchy_schwarz_density (R : ℕ → ℕ)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfirst : ∀ᶠ X : ℕ in Filter.atTop,
      a * (X : ℝ) * Real.sqrt (X : ℝ) / Real.log (X : ℝ) ≤
        Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ)))
    (hsecond : ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) ^ 2)
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
      c * X ≤ (((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3))).card : ℝ) := by
  sorry

/-- LEAF 5, the complement identity.  The representable count inside `[1, X]` is `X - euExc X`:
the interval has `X` elements and `euExc X` counts the rest of it.  No estimate, and no
hypothesis.  At `X = 0` both sides are `0`. -/
theorem leaf_card_eq_complement (X : ℕ) :
    ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3))).card = X - euExc X := by
  sorry

/-- The sealed statement of `route_euler_positive_density`, assembled from the five leaves above
with no use of the route theorem itself. -/
theorem route_euler_positive_density_split :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop, c * X ≤ ((X - euExc X : ℕ) : ℝ) := by
  obtain ⟨R, -, hR⟩ := leaf_representation_multiplicity
  obtain ⟨a, ha, hfirst⟩ := leaf_first_moment_card R hR
  obtain ⟨b, hb, hsecond⟩ := leaf_second_moment_card R hR
  obtain ⟨c, hc, hcard⟩ := leaf_cauchy_schwarz_density R hR a b ha hb hfirst hsecond
  refine ⟨c, hc, ?_⟩
  filter_upwards [hcard] with X hX
  rw [← leaf_card_eq_complement X]
  exact hX

end LeanLab.OpenProblems.State1612

#print axioms LeanLab.OpenProblems.State1612.leaf_representation_multiplicity
#print axioms LeanLab.OpenProblems.State1612.leaf_first_moment_card
#print axioms LeanLab.OpenProblems.State1612.leaf_second_moment_card
#print axioms LeanLab.OpenProblems.State1612.leaf_cauchy_schwarz_density
#print axioms LeanLab.OpenProblems.State1612.leaf_card_eq_complement
#print axioms LeanLab.OpenProblems.State1612.route_euler_positive_density_split
