import LeanLab.AlmostPrimeSums.RosserAnalytic

/-!
AI wrote this Lean code for the OMOS split of `rosser_upper_defect_moment_exp`.

Goldbach is open. No new definition, structure, class or instance is introduced
here, and the sealed statement of `rosser_upper_defect_moment_exp` is not used.

The sealed target asks for one uniform exponential decay bound for the upper
Rosser defect moment on the doubly restricted divisor set (`D` at most `n z^2`
and at least nine prime factors). The split below cuts it by the size of the
level ratio `s = log D / log z`, which is at least ten on the whole hypothesis
set because `z ^ 10 ≤ D` and `2 ≤ z`, and then cuts the deep range into the two
disjoint halves `n ≤ z ^ (s - 1)` and `n > z ^ (s - 1)` of the same divisor set.

Three leaves result, and the assembly is one arithmetic case analysis over them.
Every summand of the sealed sum is nonnegative (`s.selbergTerms` is positive on
the divisors of the sifting product and `rosserDefect` is nonnegative), so each
leaf bounds a sub-sum of the sealed sum and is strictly weaker than the target.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real ArithmeticFunction BoundingSieve

/-- LEAF. Moderate level ratio `10 ≤ log D / log z ≤ 100`. The upper Rosser
defect moment on the two-fold restricted divisor set is at most a constant,
depending only on the density parameter, times `exp (-(log D / log z))`.

This is the shallow half of the split. It is the range in which the level
`D` stays inside a fixed power of `z`, so the stopping construction of the
Rosser weights is only iterated a bounded number of times; the constant has to
absorb that fixed number of iterations but not the growth of `z`. The
hypothesis `log D / log z ≤ 100` is extra compared with the sealed statement,
which is what makes this strictly easier than the target. -/
theorem upper_defect_moment_exp_level_le (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      log D / log z ≤ 100 →
      (∑ n ∈ s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect D true n) ≤ C * exp (-(log D / log z)) := by
  sorry

/-- LEAF. Deep level ratio with `n` small, that is `n ≤ z ^ (log D / log z - 1)`
inside the two-fold restricted divisor set, and `100 ≤ log D / log z`.

This is the first half of the deep range: the divisors still carry at least
nine prime factors and are still at least `D / z^2`, but they are at most
`z^(s-1)`, so the Selberg mass of every term is still spread over a range that
the density hypothesis sees. It bounds a sub-sum of the sealed sum, all of
whose summands are nonnegative, and it carries both the depth hypothesis and
the upper restriction on `n`; it is therefore strictly easier than the target
on two counts. -/
theorem upper_defect_moment_exp_level_ge_small_n (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      100 ≤ log D / log z →
      (∑ n ∈ (s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card)).filter
          (fun n : ℕ => (n : ℝ) ≤ z ^ (log D / log z - 1)),
        s.selbergTerms n * rosserDefect D true n) ≤ C * exp (-(log D / log z)) := by
  sorry

/-- LEAF. Deep level ratio with `n` large, that is `z ^ (log D / log z - 1) < n`
inside the two-fold restricted divisor set, and `100 ≤ log D / log z`.

This is the second half of the deep range. Here a divisor of the squarefree
sifting product above `z^(s-1)` must have at least `s - 1` prime factors, and
each of its Selberg weights is a product of at least `s - 1` local factors of
size below one; this is where the factorial decay that powers the exponential
error sits. The summands are nonnegative, so this bounds a sub-sum of the
sealed sum, and it carries the depth hypothesis and the lower restriction on
`n`; it is strictly easier than the target on two counts. -/
theorem upper_defect_moment_exp_level_ge_large_n (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      100 ≤ log D / log z →
      (∑ n ∈ (s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card)).filter
          (fun n : ℕ => ¬ ((n : ℝ) ≤ z ^ (log D / log z - 1))),
        s.selbergTerms n * rosserDefect D true n) ≤ C * exp (-(log D / log z)) := by
  sorry

/-- The sealed upper defect moment bound, assembled from the three leaves by a
case analysis on the level ratio and on the size of the divisor. The summands
are nonnegative throughout, so splitting the restricted divisor set into the
two halves `n ≤ z ^ (s - 1)` and `n > z ^ (s - 1)` leaves the moment unchanged,
and the three leaf constants are added. -/
theorem rosser_upper_defect_moment_exp_split (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∑ n ∈ s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect D true n) ≤ C * exp (-(log D / log z)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := upper_defect_moment_exp_level_le K hK
  obtain ⟨C₂, hC₂, h₂⟩ := upper_defect_moment_exp_level_ge_small_n K hK
  obtain ⟨C₃, hC₃, h₃⟩ := upper_defect_moment_exp_level_ge_large_n K hK
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
      (f := fun n : ℕ => s.selbergTerms n * rosserDefect D true n)
    rw [← hsplit]
    refine (add_le_add (h₂ s z D hz hBz hD hP hden hS)
      (h₃ s z D hz hBz hD hP hden hS)).trans ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) hE

end LeanLab.AlmostPrimeSums.Decomp1527b
