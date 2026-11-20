import LeanLab.AlmostPrimeSums.RosserAnalytic
import LeanLab.AlmostPrimeSums.Tail586Deep

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

This is the second half of the deep range. A divisor of the squarefree sifting
product above `z^(s-1)` must have at least `s - 1` prime factors, but that alone
gives no decay: `LinearDensity` only yields `(1 - ν p)⁻¹ ≤ 1 + K / log p`, so
the local Selberg weight `ν p/(1 - ν p)` may exceed `1 + K / log p` and `ν p`
may reach `1/2`, and the Selberg mass `∑ p, s.selbergTerms p` grows like
`K π(z)/log z`, a positive power of `log z`. The decay comes from the
cancellation inside `rosserDefect D true n`, and its cheapest quantitative form
in this tree is the Rankin count quoted in
`upper_defect_moment_exp_level_ge_large_n_of_mass` below: the level ratio must
dominate that Selberg mass. The repaired statement is proved there with
constant `1`; supplying its hypothesis from the hypotheses above is the
Buchstab iteration (IK Lemma 6.3, Theorem 6.9), which is not in this file's
imports. The summands are nonnegative, so this bounds a sub-sum of the sealed
sum. -/
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

/-- The repaired form of the leaf above, and the reason the leaf is not
disposable: under the one extra hypothesis that the level ratio dominates the
total Rosser mass `R = ∑ p, s.selbergTerms p`, the very same slice obeys the
sealed decay with `C = 1`.

The proof is `Tail586Deep.rosser_large_divisor_mass_exp586`: `rosserDefect` is
at most `2 ^ ω n` in absolute value, the level cut `z ^ (L - 1) < n` forces
`L - 1 < ω n`, and the `z ^ ω` weighted Selberg mass is the Euler product
`∏ (1 + U * s.selbergTerms p)`, so the slice costs `exp (-2 (L - 1))` times
`exp (2 e² R)`. That is where the cancellation in `rosserDefect` is spent, and
the constant `2 + 2 e² R ≤ L` is exactly what it leaves over. -/
theorem upper_defect_moment_exp_level_ge_large_n_of_mass (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      100 ≤ log D / log z →
      2 + (2 * exp 2) * (∑ p ∈ s.prodPrimes.primeFactors, s.selbergTerms p) ≤
        log D / log z →
      (∑ n ∈ (s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card)).filter
          (fun n : ℕ => ¬ ((n : ℝ) ≤ z ^ (log D / log z - 1))),
        s.selbergTerms n * rosserDefect D true n) ≤ C * exp (-(log D / log z)) := by
  refine ⟨1, one_pos, ?_⟩
  intro s z D hz hBz hD hP hden hL hS
  have hz1 : 1 < z := by linarith
  have hrank := rosser_large_divisor_mass_exp586 s D z (log D / log z) hz1 hP hS true
  have hsub : ∀ n ∈ ((s.prodPrimes.divisors.filter
        (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card)).filter
        (fun n : ℕ => ¬ ((n : ℝ) ≤ z ^ (log D / log z - 1)))),
      n ∈ s.prodPrimes.divisors.filter
        (fun n : ℕ => z ^ (log D / log z - 1) < n) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn1).1, not_le.mp hn2⟩
  have hnonneg : ∀ n ∈ s.prodPrimes.divisors.filter
        (fun n : ℕ => z ^ (log D / log z - 1) < n),
      n ∉ ((s.prodPrimes.divisors.filter
        (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card)).filter
        (fun n : ℕ => ¬ ((n : ℝ) ≤ z ^ (log D / log z - 1)))) →
      0 ≤ s.selbergTerms n * rosserDefect D true n := by
    intro n hn _
    have hdvd : n ∣ s.prodPrimes := (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1).1
    exact mul_nonneg (s.selbergTerms_pos hdvd).le (rosserDefect_nonneg D true n)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg).trans (by simpa using hrank)

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
