import LeanLab.OpenProblems.State1612

/-!
# Split of `route_euler_almost_all` (OpenProblems, State1612)

The target says the exception count `euExc X` is `o(X)`. This file reduces it to four strictly
easier leaves and assembles the target from them without any of the four.

The route, written out.  Write `m_n = 8n + 3`.  A representation `m = x ^ 2 + 2 * p` has `x` odd,
and the list form `4n + 1 = p + 2k(k+1)` of the source file is a bijection, so a multiplicity
`R n`, the number of `k` with `4n + 1 - 2k(k+1)` prime, vanishes exactly at the exceptions.

1. `leaf_representation_multiplicity`: such an `R`, given by a finite list search, exists.
2. `leaf_circle_method_variance`: the mean value of `R` on a scale is a main term `m` of size at
   least a fixed multiple of `sqrt n / log n`, and the second moment of `R - m` over `[1, X]` is
   at most a constant times `X ^ 2 / (log X) ^ 3`.  The shrinking of the second moment leaves a
   `log X` to spare against the square of the main term.
3. `leaf_exception_count_dyadic`: the level-set estimate.  An `n` counted by `euExc` has `R` at `0`
   and the main term at least `c / log X`, so the second moment controls the count, and at the
   scales `X = 2 ^ k` the count is below `epsilon * X` for every positive `epsilon`.
4. `leaf_dyadic_to_all_X`: `euExc` is monotone and each `X` sits in `[2 ^ k, 2 ^ (k+1))`, so the
   estimate at the powers of two carries to every `X` with `epsilon` halved.
-/

namespace LeanLab.OpenProblems.State1612

open LeanLab

/-- LEAF 1, multiplicity.  There is a multiplicity `R n`, computed from the list form as the
number of `k` with `4n + 1 - 2k(k+1)` prime, and for `1 ≤ n` it vanishes exactly where `8n + 3`
has no odd square plus twice a prime.  The bound `4n + 2` on `k` is safe: a term with
`2k(k+1) > 4n + 1` truncates to `0`, which is not prime, and every true solution has `k ≤ n`. -/
theorem leaf_representation_multiplicity :
    ∃ R : ℕ → ℕ,
      (∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
          (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card) ∧
      ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)) := by
  sorry

/-- LEAF 2, mean value and second moment.  For the multiplicity `R` of LEAF 1 there are a main
term `m`, positive constants `B` and `c`, with `m n` at least `c * sqrt n / log n` on `1 ≤ n` and
the second moment of `R - m` over `[1, X]` at most `B * X ^ 2 / (log X) ^ 3`.  This is the only
analytic input of the route: the sum over the circle is dominated except near rationals with small
denominator, the singular series is bounded below so the main term keeps a fixed fraction of
`sqrt n / log n`, and the mean square of the error gains a whole power of the logarithm. -/
theorem leaf_circle_method_variance (R : ℕ → ℕ)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) :
    ∃ (m : ℕ → ℝ) (B c : ℝ), 0 < B ∧ 0 < c ∧
      (∀ n : ℕ, 1 ≤ n → c * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ m n) ∧
      ∀ᶠ X : ℕ in Filter.atTop,
        Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2) ≤
          B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3 := by
  sorry

/-- LEAF 3, level set at the powers of two.  With the multiplicity of LEAF 1 and the main term and
second moment of LEAF 2, every positive `epsilon` has the exceptions below `epsilon * 2 ^ k` for
all large `k`.  A counted `n ≤ X = 2 ^ k` satisfies `R n = 0`, so `(R n - m n) ^ 2 = (m n) ^ 2` and
`m n` is at least `c / log X`; the second moment then bounds the count by `(B / c ^ 2) * X / log X`,
and `log X` grows without bound while `B / c ^ 2` stays fixed. -/
theorem leaf_exception_count_dyadic (R : ℕ → ℕ) (m : ℕ → ℝ) (B c : ℝ)
    (hB : 0 < B) (hc : 0 < c)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)))
    (hmain : ∀ n : ℕ, 1 ≤ n → c * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ m n)
    (hvar : ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2) ≤
        B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in Filter.atTop, (euExc (2 ^ k) : ℝ) ≤ ε * ((2 ^ k : ℕ) : ℝ) := by
  sorry

/-- LEAF 4, from the powers of two to every `X`.  If the exceptions at `2 ^ k` are below
`epsilon * 2 ^ k` for all large `k`, then the exceptions at every `X` are below `epsilon * X` for
all large `X`: `euExc` is monotone, and for `1 ≤ X` there is `k` with `2 ^ k ≤ X < 2 ^ (k+1)`, so
`euExc X ≤ euExc (2 ^ (k+1)) ≤ (epsilon / 2) * 2 ^ (k+1) ≤ epsilon * X`.  The bound at `X = 0` and
`X = 1` is covered by taking the threshold large. -/
theorem leaf_dyadic_to_all_X
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in Filter.atTop, (euExc (2 ^ k) : ℝ) ≤ ε * ((2 ^ k : ℕ) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in Filter.atTop, (euExc X : ℝ) ≤ ε * X := by
  sorry

/-- The sealed statement of `route_euler_almost_all`, assembled from the four leaves above. -/
theorem route_euler_almost_all_split :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in Filter.atTop, (euExc X : ℝ) ≤ ε * X := by
  refine leaf_dyadic_to_all_X ?_
  intro ε hε
  obtain ⟨R, -, hR⟩ := leaf_representation_multiplicity
  obtain ⟨m, B, c, hB, hc, hmain, hvar⟩ := leaf_circle_method_variance R hR
  exact leaf_exception_count_dyadic R m B c hB hc hR hmain hvar ε hε

end LeanLab.OpenProblems.State1612
