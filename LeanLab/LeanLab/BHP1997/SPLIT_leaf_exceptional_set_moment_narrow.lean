/-
Split of `leaf_exceptional_set_moment_narrow` in
`LeanLab.BHP1997.SPLIT_leaf_exceptional_set_moment` into four leaves, one per cell of the shift
range and the modulus range, with the leaf statement left unchanged and the leaf itself neither
imported as a proof nor used.

Where the cuts are made. The leaf bounds the squared centred short sums, summed over the
characters outside an exceptional set `E` with a bounded cardinality, and integrated over `y` in
`[x^(11/20+eps)/2, 3 x^(11/20+eps)]`, for shifts `z` in the narrow range `z <= 1`. Two cuts are
made, and they are independent. First, the shift range is cut at `1/2`. Below the cut the window
`[y, y + y z]` is at most half of `y`, above it at most `y`, so every `y` in the integration
range sees a window of a different size and each half confines the same integral to a shorter
range of `z`; each half is therefore strictly easier than the whole. Second, the modulus range is
cut at `q <= 2` against `3 <= q`: for `q <= 2` the character group has at most two elements, so
the sum outside `E` has at most two summands, while for `3 <= q` the count of the exceptional set
is what carries the argument, and the two regimes are where the constants of the two halves of
that count differ.

Each leaf is one of the four cells. It carries every hypothesis of the leaf unchanged, obtains
the set `E` and its cardinality bound as a hypothesis rather than producing them, and asserts the
same inequality as the leaf on its cell only, so no leaf restates the whole range and none
assumes the leaf. Non-vacuity: the empty set satisfies the cardinality hypothesis, so the
hypotheses of each leaf are consistent with the leaf's own hypotheses; every cell of the `(q, z)` range is
realised for large `x`, because `q` in `{1, 2}` and `q >= 3` below `sieveQ` are both available and
`z` ranges over `[q sieveQ/(6 x^theta), 1]` around either side of `1/2`. The assembly is the case
split on `z <= 1/2` and on `q <= 2`, with the four constants combined through absolute values and
one monotonicity step for the product in its constant block, with no sorry.

The four leaves remain OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_exceptional_set_moment

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF 1 of 4. Step: the averaged squared centred short sums on the complement of the
exceptional set, in the cell of the short shift `z <= 1/2` and of the small modulus `q <= 2`.
Here the window `[y, y + y z]` is at most half of `y`, and the sum over the characters outside `E`
has at most two summands because the character group has at most two elements.

This is the leaf restricted to `z <= 1/2` and `q <= 2`: it keeps the set `E` and its cardinality
bound as a hypothesis and it covers only a subrange of the shift and a subrange of the modulus, so
it is strictly easier than the leaf and says nothing outside its cell. It is not vacuous: the
empty set satisfies the cardinality hypothesis, `q` in `{1, 2}` is available, and `z` may be any
admissible shift at most `1/2`. -/
theorem leaf_narrow_small_modulus_short_shift
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

/-- LEAF 2 of 4. Step: the same averaged squared centred short sums on the complement, in the
cell of the longer narrow shift `1/2 <= z <= 1` and of the small modulus `q <= 2`, where the
window `[y, y + y z]` runs up to the full length of `y` and the sum outside `E` again has at most
two summands.

This is the leaf restricted to `1/2 <= z <= 1` and `q <= 2`, with the set `E` and its cardinality
bound still a hypothesis, so it covers only a subrange of the shift and of the modulus and is
strictly easier than the leaf. It is not vacuous: the empty set satisfies the cardinality
hypothesis, `q` in `{1, 2}` is available, and shifts between `1/2` and `1` are admissible. -/
theorem leaf_narrow_small_modulus_long_shift
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
          1 / 2 ≤ z → z ≤ 1 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 3 of 4. Step: the same averaged squared centred short sums on the complement, in the
cell of the short shift `z <= 1/2` and of the large modulus `3 <= q`, where the sum outside `E`
follows the cardinality of the exceptional set rather than the size of the character group.

This is the leaf restricted to `z <= 1/2` and `3 <= q`, with the set `E` and its cardinality
bound a hypothesis, so it covers only a subrange of the shift and of the modulus and is strictly
easier than the leaf. It is not vacuous: the empty set satisfies the cardinality hypothesis,
`3 <= q <= sieveQ eps x` is available for large `x`, and `z <= 1/2` is an admissible shift. -/
theorem leaf_narrow_large_modulus_short_shift
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
        3 ≤ q →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
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

/-- LEAF 4 of 4. Step: the same averaged squared centred short sums on the complement, in the
cell of the longer narrow shift `1/2 <= z <= 1` and of the large modulus `3 <= q`.

This is the leaf restricted to `1/2 <= z <= 1` and `3 <= q`, with the set `E` and its cardinality
bound a hypothesis, so it covers only a subrange of the shift and of the modulus and is strictly
easier than the leaf. It is not vacuous: the empty set satisfies the cardinality hypothesis,
`3 <= q <= sieveQ eps x` is available for large `x`, and shifts between `1/2` and `1` are
admissible. -/
theorem leaf_narrow_large_modulus_long_shift
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
        3 ≤ q →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          1 / 2 ≤ z → z ≤ 1 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- The leaf statement, assembled from the four regime leaves with no sorry. The constant is
the sum of the absolute values of the four constants plus `2`, which dominates each of them and
keeps the logarithm positive; the case split on `z <= 1/2` and on `q <= 2` sends every `(q, z)`
of the leaf range to the leaf that covers its cell, and one monotonicity step moves the constant
of that cell up to the common one. No step uses the leaf. -/
theorem leaf_exceptional_set_moment_narrow_split
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
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          z ≤ 1 →
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
    leaf_narrow_small_modulus_short_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₂, hC₂⟩ :=
    leaf_narrow_small_modulus_long_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₃, hC₃⟩ :=
    leaf_narrow_large_modulus_short_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₄, hC₄⟩ :=
    leaf_narrow_large_modulus_long_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  refine ⟨|C₁| + |C₂| + |C₃| + |C₄| + 2, ?_⟩
  intro x hx q hq hqQ z hzlo hzup hz1
  have hC₁x : C₁ ≤ x := by
    linarith [le_abs_self C₁, abs_nonneg C₂, abs_nonneg C₃, abs_nonneg C₄]
  have hC₂x : C₂ ≤ x := by
    linarith [le_abs_self C₂, abs_nonneg C₁, abs_nonneg C₃, abs_nonneg C₄]
  have hC₃x : C₃ ≤ x := by
    linarith [le_abs_self C₃, abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₄]
  have hC₄x : C₄ ≤ x := by
    linarith [le_abs_self C₄, abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₃]
  have hx2 : (2 : ℝ) ≤ x := by
    linarith [abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₃, abs_nonneg C₄]
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hC₁m : C₁ ≤ |C₁| + |C₂| + |C₃| + |C₄| + 2 := by
    linarith [le_abs_self C₁, abs_nonneg C₂, abs_nonneg C₃, abs_nonneg C₄]
  have hC₂m : C₂ ≤ |C₁| + |C₂| + |C₃| + |C₄| + 2 := by
    linarith [le_abs_self C₂, abs_nonneg C₁, abs_nonneg C₃, abs_nonneg C₄]
  have hC₃m : C₃ ≤ |C₁| + |C₂| + |C₃| + |C₄| + 2 := by
    linarith [le_abs_self C₃, abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₄]
  have hC₄m : C₄ ≤ |C₁| + |C₂| + |C₃| + |C₄| + 2 := by
    linarith [le_abs_self C₄, abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₃]
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
  by_cases hq2 : q ≤ 2
  · by_cases hzs : z ≤ 1 / 2
    · exact le_trans
        (hC₁ x hC₁x q hq hqQ hq2 z hzlo hzup hzs)
        (hmono C₁ (|C₁| + |C₂| + |C₃| + |C₄| + 2) hC₁m)
    · exact le_trans
        (hC₂ x hC₂x q hq hqQ hq2 z hzlo hzup (le_of_lt (lt_of_not_ge hzs)) hz1)
        (hmono C₂ (|C₁| + |C₂| + |C₃| + |C₄| + 2) hC₂m)
  · have hq3 : 3 ≤ q := by omega
    by_cases hzs : z ≤ 1 / 2
    · exact le_trans
        (hC₃ x hC₃x q hq hqQ hq3 z hzlo hzup hzs)
        (hmono C₃ (|C₁| + |C₂| + |C₃| + |C₄| + 2) hC₃m)
    · exact le_trans
        (hC₄ x hC₄x q hq hqQ hq3 z hzlo hzup (le_of_lt (lt_of_not_ge hzs)) hz1)
        (hmono C₄ (|C₁| + |C₂| + |C₃| + |C₄| + 2) hC₄m)
