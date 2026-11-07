import LeanLab.AlmostPrimeSums.RosserAnalytic

/-!
Split of the sealed lower Rosser defect moment bound.

Goldbach is open. No new definition, structure, class, instance or notation is
introduced here, and the sealed statement of `rosser_lower_defect_moment_exp`
is neither used nor assumed.

The sealed target asks for one uniform exponential decay bound for the lower
Rosser defect moment on the doubly restricted divisor set: divisors of the
sifting product that are at least `D / z ^ 2` and carry at least nine prime
factors. The split cuts it by the size of the level ratio `s = log D / log z`,
which is at least ten on the whole hypothesis set because `z ^ 10 ≤ D` and
`2 ≤ z`, and then cuts the deep range into the two disjoint halves
`n ≤ z ^ (s - 1)` and `n > z ^ (s - 1)` of the same divisor set.

Each of the three leaves restricts the range of `s` (and, in the deep range,
restricts `n`), so each leaf bounds a sub-sum of the sealed sum over a strictly
smaller index set: a leaf is a consequence of the target and is strictly
easier than it. The assembly is one arithmetic case analysis over the leaves;
splitting a finite sum with `Finset.sum_filter_add_sum_filter_not` is exact and
needs no sign hypothesis, and the three constants are added.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real ArithmeticFunction BoundingSieve

/-- LEAF. The shallow half of the split, for a level ratio at most `100`. For a
lower defect moment the level `D` then stays inside a fixed power of `z`, so
the stopping construction behind the Rosser weights is iterated only a bounded
number of times and the constant has to absorb that fixed number of iterations
but not the growth of `z`. The extra hypothesis `log D / log z ≤ 100` restricts
the range of the sealed statement, which is what makes this bound strictly
easier than the target. -/
theorem lower_defect_moment_exp_level_le (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      log D / log z ≤ 100 →
      (∑ n ∈ s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect D false n) ≤ C * exp (-(log D / log z)) := by
  sorry

/-- LEAF. The first half of the deep range: level ratio at least `100` and
`n ≤ z ^ (log D / log z - 1)` inside the doubly restricted divisor set. The
divisors still carry at least nine prime factors and are still at least
`D / z ^ 2`, but they sit below `z ^ (s - 1)`, so the Selberg mass of each term
is spread over a range that the density hypothesis sees. This bounds a sub-sum
of the sealed sum over a strictly smaller index set and carries both the depth
hypothesis and the upper restriction on `n`, so it is easier than the target on
two counts. -/
theorem lower_defect_moment_exp_level_ge_small_n (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      100 ≤ log D / log z →
      (∑ n ∈ (s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card)).filter
          (fun n : ℕ => (n : ℝ) ≤ z ^ (log D / log z - 1)),
        s.selbergTerms n * rosserDefect D false n) ≤ C * exp (-(log D / log z)) := by
  sorry

/-- LEAF. The second half of the deep range: level ratio at least `100` and
`z ^ (log D / log z - 1) < n` inside the doubly restricted divisor set. Here a
divisor of the squarefree sifting product above `z ^ (s - 1)` has at least
`s - 1` prime factors, and each of its Selberg weights is a product of at least
`s - 1` local factors of size below one; this is where the factorial decay that
produces the exponential error sits. This bounds a sub-sum of the sealed sum
over a strictly smaller index set and carries the depth hypothesis and the
lower restriction on `n`, so it is easier than the target on two counts. -/
theorem lower_defect_moment_exp_level_ge_large_n (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      100 ≤ log D / log z →
      (∑ n ∈ (s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card)).filter
          (fun n : ℕ => ¬ ((n : ℝ) ≤ z ^ (log D / log z - 1))),
        s.selbergTerms n * rosserDefect D false n) ≤ C * exp (-(log D / log z)) := by
  sorry

/-- The sealed lower defect moment bound, assembled from the three leaves by a
case analysis on the level ratio and on the size of the divisor. Splitting the
restricted divisor set into the two halves `n ≤ z ^ (s - 1)` and
`n > z ^ (s - 1)` is an identity for a finite sum, so the moment is unchanged,
and the three leaf constants are added. -/
theorem rosser_lower_defect_moment_exp_split (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∑ n ∈ s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect D false n) ≤ C * exp (-(log D / log z)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := lower_defect_moment_exp_level_le K hK
  obtain ⟨C₂, hC₂, h₂⟩ := lower_defect_moment_exp_level_ge_small_n K hK
  obtain ⟨C₃, hC₃, h₃⟩ := lower_defect_moment_exp_level_ge_large_n K hK
  refine ⟨C₁ + C₂ + C₃, by linarith, ?_⟩
  intro s z D hz hBz hD hP hden
  have hE : 0 ≤ exp (-(log D / log z)) := (exp_pos _).le
  rcases le_total (log D / log z) 100 with hS | hS
  · exact (h₁ s z D hz hBz hD hP hden hS).trans
      (mul_le_mul_of_nonneg_right (by linarith) hE)
  · have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := s.prodPrimes.divisors.filter
        (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card))
      (p := fun n : ℕ => (n : ℝ) ≤ z ^ (log D / log z - 1))
      (f := fun n : ℕ => s.selbergTerms n * rosserDefect D false n)
    rw [← hsplit]
    refine (add_le_add (h₂ s z D hz hBz hD hP hden hS)
      (h₃ s z D hz hBz hD hP hden hS)).trans ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) hE

end LeanLab.AlmostPrimeSums.Decomp1527b
