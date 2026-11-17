import LeanLab.HelfgottMajor.SPLIT_zero_multiplicity_subexponential

/-!
Split of `book_count_le_main_add_error` of `HelfgottMajor`.

The target is the one sided explicit zero count of book page 431: for every character of modulus
`q`, primitive or not, and every height `T` at least `100`, the multiplicity weighted count of
the zeros of `L (·, χ)` in the open strip up to height `T` is at most the main term `bookMain q T`
plus the error `bookError q T`.

For a primitive character the count is the two sided estimate `ZeroCount1623.book_zero_count`,
which puts the count within `bookError` of `bookMain`; the one sided form is its upper half and it
is the first leaf.

The remaining content is the character. The target quantifies over imprimitive characters as
well. An imprimitive character of modulus `q` is induced from its primitive character of
conductor `c = χ.conductor`, which divides `q`, and the two L functions differ by the finitely
many Euler factors `1 - χ₀ p ^ (-s)` at the primes dividing `q` but not `c`. Each of those
factors is nonzero on the open right half plane, so it removes no zero and adds none: the strip
zeros agree as sets, leaf two, and with multiplicity, leaf three. The conductor is at most the
modulus, and both the main term and the error are nondecreasing in the modulus at a fixed height
of at least `100`, leaf four, so the count at the conductor is dominated by the count at the
modulus.

The assembly is the case split on primitivity. The primitive case is the first leaf; the
imprimitive case transports the count at the conductor to the modulus with leaves two and three,
estimates it with the first leaf at the conductor, and dominates the result with leaf four.
`book_count_le_main_add_error` itself is not used.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. The primitive case: the one sided count. For a primitive character of modulus `q` and
height at least `100` the multiplicity weighted strip count is at most the main term plus the
error. This is the upper half of the two sided explicit estimate, which is stated for heights at
least one, so it applies here; no zero of `L` is exhibited. -/
theorem book_count_le_main_add_error_of_isPrimitive (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (hT : 100 ≤ T) :
    ZeroCount1623.bookCount χ T ≤ ZeroCount1623.bookMain q T + ZeroCount1623.bookError q T := by
  have h := (abs_le.mp (ZeroCount1623.book_zero_count χ hχ (T := T) (by linarith))).2
  linarith

/-- LEAF. The strip zero sets of an imprimitive character and of the primitive character that
induces it coincide. The two L functions differ by the Euler factors of the primes dividing the
modulus but not the conductor, and each of those factors is nonzero on the open right half
plane, so a point of the open strip is a zero of one exactly when it is a zero of the other. -/
theorem stripZeros_primitiveCharacter (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (T : ℝ) :
    ZeroCount1623.stripZeros χ T = ZeroCount1623.stripZeros χ.primitiveCharacter T := by
  sorry

/-- LEAF. The multiplicities of a strip zero of an imprimitive character and of the same point as
a zero of the inducing primitive character agree. The extra Euler factors are analytic and
nonzero at the point, so multiplying by them changes no order of vanishing. -/
theorem mult_eq_primitiveCharacter (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    ZeroCount1623.mult χ ρ = ZeroCount1623.mult χ.primitiveCharacter ρ := by
  sorry

/-- LEAF. The main term plus the error is nondecreasing in the modulus. At a fixed height of at
least `100` both the main term `T / (2 π)` times a logarithm of a positive multiple of `q` and
the error `0.15` times a logarithm of a positive multiple of `q` increase with `q`, so raising
the modulus raises the bound. -/
theorem bookMain_add_bookError_mono {q₀ q : ℕ} {T : ℝ} (hq0 : 1 ≤ q₀) (hq : q₀ ≤ q)
    (hT : 100 ≤ T) :
    ZeroCount1623.bookMain q₀ T + ZeroCount1623.bookError q₀ T ≤
      ZeroCount1623.bookMain q T + ZeroCount1623.bookError q T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hc : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  have hcast : (q₀ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0R : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast (by omega : 0 < q₀)
  have harg : (q₀ : ℝ) * T ≤ (q : ℝ) * T := by
    exact mul_le_mul_of_nonneg_right hcast hT0.le
  have hle1 : (q₀ : ℝ) * T / (2 * Real.pi * Real.exp 1) ≤
      (q : ℝ) * T / (2 * Real.pi * Real.exp 1) := by
    exact div_le_div_of_nonneg_right harg hc.le
  have hpos0 : (0 : ℝ) < (q₀ : ℝ) * T := mul_pos hq0R hT0
  have hpos : (0 : ℝ) < (q : ℝ) * T := mul_pos (lt_of_lt_of_le hq0R hcast) hT0
  have hlog1 : Real.log ((q₀ : ℝ) * T / (2 * Real.pi * Real.exp 1)) ≤
      Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) :=
    Real.log_le_log (div_pos hpos0 hc) hle1
  have hmain : T / (2 * Real.pi) * Real.log ((q₀ : ℝ) * T / (2 * Real.pi * Real.exp 1)) ≤
      T / (2 * Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) :=
    mul_le_mul_of_nonneg_left hlog1 (div_nonneg hT0.le (by positivity))
  have hlog2 : Real.log ((q₀ : ℝ) * T) ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log hpos0 harg
  have herr : 0.15 * Real.log ((q₀ : ℝ) * T) + 3.389 ≤ 0.15 * Real.log ((q : ℝ) * T) + 3.389 := by
    linarith [mul_le_mul_of_nonneg_left hlog2 (by norm_num : (0 : ℝ) ≤ 0.15)]
  unfold ZeroCount1623.bookMain ZeroCount1623.bookError
  linarith [hmain, herr]

/-- The target, from the four steps. For a primitive character it is the first leaf. Otherwise
the conductor is a positive divisor of the modulus, so the primitive character of the conductor is
primitive, its count equals the count at the modulus by the two zero set leaves, and the bound at
the conductor is at most the bound at the modulus by the monotonicity leaf. -/
theorem book_count_le_main_add_error_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 100 ≤ T) :
    ZeroCount1623.bookCount χ T ≤ ZeroCount1623.bookMain q T + ZeroCount1623.bookError q T := by
  by_cases hχ : χ.IsPrimitive
  · exact book_count_le_main_add_error_of_isPrimitive q χ hχ T hT
  · have hcond : χ.conductor ≠ 0 := χ.conductor_ne_zero
    haveI : NeZero χ.conductor := ⟨hcond⟩
    have hcount : ZeroCount1623.bookCount χ T =
        ZeroCount1623.bookCount χ.primitiveCharacter T := by
      have hset := stripZeros_primitiveCharacter q χ T
      have hfin : (ZeroCount1623.stripZeros_finite χ T).toFinset =
          (ZeroCount1623.stripZeros_finite χ.primitiveCharacter T).toFinset := by
        ext ρ
        simp only [Set.Finite.mem_toFinset, hset]
      unfold ZeroCount1623.bookCount
      rw [hfin]
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hmemχ : ρ ∈ (ZeroCount1623.stripZeros_finite χ T).toFinset := by
        have h := (Finset.mem_filter.mp hρ).1
        simpa only [hfin] using h
      have hmem : ρ ∈ ZeroCount1623.stripZeros χ T :=
        (ZeroCount1623.stripZeros_finite χ T).mem_toFinset.mp hmemχ
      rw [mult_eq_primitiveCharacter q χ hmem.2.1 hmem.2.2.1 hmem.1]
    rw [hcount]
    have hle := book_count_le_main_add_error_of_isPrimitive χ.conductor χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive T hT
    refine le_trans hle (bookMain_add_bookError_mono ?_ ?_ hT)
    · exact Nat.pos_of_ne_zero hcond
    · exact Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level

end LeanLab.HelfgottMajor.Decomp269c
