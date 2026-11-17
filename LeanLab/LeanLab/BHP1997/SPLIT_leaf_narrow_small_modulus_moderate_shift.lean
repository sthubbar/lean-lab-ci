/-
Split of `leaf_narrow_small_modulus_moderate_shift` in
`LeanLab.BHP1997.SPLIT_leaf_narrow_small_modulus_short_shift` into two bands. That goal is itself the
upper cell `2 (sieveQ ε x) / x^(11/20+ε) <= z`, `z <= 1/2`, of
`leaf_narrow_small_modulus_short_shift`. Nothing here reaches outside the cell: both leaves keep
every hypothesis of the target and add one further bound on `z` from above or from below, and the
target statement is neither imported as a proof nor used in the assembly.

Where the second cut is made, and why there. With `q <= 2` and `z <= 6 q (sieveQ ε x) /
x^(11/20+ε)`, the admissible shift range of this cell is `2 Q / X <= z <= 12 Q / X` with
`Q = sieveQ ε x` and `X = x^(11/20+ε)`, so throughout the cell the window `[y, y + y z]` spans
between two and twelve cutoffs of length `Q`. The cut is placed inside that range at `z = 4 Q / X`:
below it the window spans two to four cutoffs, a bounded number of them, and the coefficient family
is met through one fixed stretch of consecutive integers of that size; above it the window spans
four to twelve cutoffs, and any bound has to survive the cancellation across several of them at
once. So each band bounds the same integral by a different route, each is the target with `z`
restricted to its band, and each keeps the set `E` and its cardinality bound as hypotheses rather
than producing them.

Non-vacuity of both bands. The empty set satisfies the cardinality hypothesis. `sieveQ ε x` is
positive and `(sieveQ ε x) / x^(11/20+ε)` tends to zero, so for every large `x` both bands are
non-empty and sit inside `z <= 1/2`: `z = 3 Q / X` lies in the lower band with `q = 1`, and
`z = 6 Q / X` lies in the upper band with `q = 1`, still below `6 q Q / X` and above the lower limit
`q Q / (6 X)`. The hypotheses of neither band are contradictory.

What is missing, said plainly so the next worker is not misled. The file this one imports records
that the whole short shift cell cannot be reached from these hypotheses: the family `v0 = 0`, `E`
empty, `b0 x m = (-1) ^ (m / Q)` with `Q = sieveQ ε x` meets the divisor bound and the centred prefix
bound, consecutive blocks cancel in a prefix, and a window sum is still of size `Q`, so the
`y`-integral is of size `Q^2 X` against a budget of `C Q^2 X (log x)^(-A)`. That family realises
every `z` in the cell, so both bands inherit the obstruction and a restriction of the shift range
cannot repair it. Closing either band needs a mean-square estimate for the coefficient family across
blocks, which `hchar` (prefixes only) and `hbd` (pointwise only) do not supply.

The assembly below is the case split on `z <= 4 (sieveQ ε x) / x^(11/20+ε)` with the constant
`|C₁| + |C₂| + 2`, and it leaves no goal open.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_narrow_small_modulus_short_shift

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF 1 of 2. Step: the lower band of the short shift cell, `2 Q / X <= z <= 4 Q / X` with
`Q = sieveQ ε x` and `X = x^(11/20+ε)`. There the window spans two to four cutoffs of length `Q`,
a bounded number of them, so the coefficient family is met through one fixed stretch of consecutive
integers of that size and the centred window sum is controlled there without any cancellation
across cutoffs. Everything above `4 Q / X` is left to LEAF 2, and `E` with its cardinality bound
stays a hypothesis, so this is strictly easier than the target and does not assume it. -/
theorem leaf_narrow_small_modulus_moderate_shift_low_band
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        q ≤ 2 →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          2 * sieveQ ε x / x ^ (11 / 20 + ε) ≤ z →
          z ≤ 4 * sieveQ ε x / x ^ (11 / 20 + ε) →
          z ≤ 1 / 2 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 2 of 2. Step: the upper band of the short shift cell, `4 Q / X <= z`, with
`Q = sieveQ ε x` and `X = x^(11/20+ε)`; together with `z <= 6 q Q / X` and `q <= 2` the band stops
at `12 Q / X`. There the window spans four to twelve cutoffs of length `Q`, so the bound is taken
across blocks of the coefficient family, where consecutive blocks cancel in pairs and only their
ends survive. Everything below `4 Q / X` is left to LEAF 1, and `E` with its cardinality bound stays
a hypothesis, so this is strictly easier than the target. -/
theorem leaf_narrow_small_modulus_moderate_shift_high_band
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        q ≤ 2 →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          2 * sieveQ ε x / x ^ (11 / 20 + ε) ≤ z →
          4 * sieveQ ε x / x ^ (11 / 20 + ε) ≤ z →
          z ≤ 1 / 2 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- The target statement, assembled from the two bands of the shift range with no open goal. The
constant is `|C₁| + |C₂| + 2`, which dominates the constant of either band; the case split on
`z <= 4 (sieveQ ε x) / x^(11/20+ε)` sends every admissible shift to the band that covers it, and one
monotonicity step moves the constant of that band up to the common one. No step uses the target
statement. -/
theorem leaf_narrow_small_modulus_moderate_shift_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        q ≤ 2 →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          2 * sieveQ ε x / x ^ (11 / 20 + ε) ≤ z →
          z ≤ 1 / 2 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C₁, hC₁⟩ :=
    leaf_narrow_small_modulus_moderate_shift_low_band h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₂, hC₂⟩ :=
    leaf_narrow_small_modulus_moderate_shift_high_band h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  refine ⟨|C₁| + |C₂| + 2, ?_⟩
  intro x hx q hq hqQ hq2 z hzlo hzup hzm hz12
  have hC₁x : C₁ ≤ x := by linarith [le_abs_self C₁, abs_nonneg C₂]
  have hC₂x : C₂ ≤ x := by linarith [le_abs_self C₂, abs_nonneg C₁]
  have hx0 : (0 : ℝ) < x := by linarith [abs_nonneg C₁, abs_nonneg C₂]
  have hlogx : (0 : ℝ) < Real.log x :=
    Real.log_pos (by linarith [abs_nonneg C₁, abs_nonneg C₂])
  have hC₁m : C₁ ≤ |C₁| + |C₂| + 2 := by linarith [le_abs_self C₁, abs_nonneg C₂]
  have hC₂m : C₂ ≤ |C₁| + |C₂| + 2 := by linarith [le_abs_self C₂, abs_nonneg C₁]
  have hK2 : (0 : ℝ) ≤ ((q : ℝ) * sieveQ ε x) ^ 2 := sq_nonneg _
  have hL2 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0.le _
  have hG2 : (0 : ℝ) ≤ Real.log x ^ (-A) := le_of_lt (Real.rpow_pos_of_pos hlogx _)
  have hmono : ∀ C C' : ℝ, C ≤ C' →
      C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
        C' * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) *
          Real.log x ^ (-A) := by
    intro C C' hCC'
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hK2) hL2) hG2
  by_cases hzs : z ≤ 4 * sieveQ ε x / x ^ (11 / 20 + ε)
  · exact le_trans
      (hC₁ x hC₁x q hq hqQ hq2 z hzlo hzup hzm hzs hz12)
      (hmono C₁ (|C₁| + |C₂| + 2) hC₁m)
  · exact le_trans
      (hC₂ x hC₂x q hq hqQ hq2 z hzlo hzup hzm (le_of_lt (lt_of_not_ge hzs)) hz12)
      (hmono C₂ (|C₁| + |C₂| + 2) hC₂m)
