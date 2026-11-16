/-
Split of `leaf_narrow_small_modulus_short_shift` in
`LeanLab.BHP1997.SPLIT_leaf_exceptional_set_moment_narrow` into two leaves, with the statement left
unchanged and the target neither imported as a proof nor used.

Where the cut is made. The target fixes `q <= 2` and `z <= 1/2`, and it also imposes
`z <= 6 q (sieveQ ε x) / x^(11/20+ε)` with `q <= sieveQ ε x`, so on the whole admissible range the
window `[y, y + y z]` is at most `36 (sieveQ ε x)` long, i.e. a fixed number of sieve cutoffs, and
the shift is never long in units of the cutoff. The only non-empty part of the shift range is
therefore the short end, and the cut is made inside it, at `z = 2 (sieveQ ε x) / x^(11/20+ε)`:
below the cut the window spans at most six cutoffs, so the coefficient family is met through one
stretch of consecutive integers of that size; above the cut the window spans between two and
thirty-six cutoffs, and any bound has to survive the cancellation across several of them. The two
regimes bound the same integral by different routes, and each is strictly easier than the target.

Each leaf keeps every hypothesis of the target unchanged, obtains the set `E` and its cardinality
bound as a hypothesis rather than producing them, and asserts the same inequality as the target on
its cell of the shift range only, so no leaf restates the whole range and none assumes the target.
Non-vacuity: the empty set satisfies the cardinality hypothesis; `q = 1` and `q = 2` both satisfy
`1 <= q <= sieveQ ε x` once `sieveQ ε x >= 2`; and both cells are realised, `z = sieveQ ε x /
x^(11/20+ε)` lying in the lower cell and `z = 4 (sieveQ ε x) / x^(11/20+ε)` in the upper one (with
`q = 2` there), for every large `x`. The assembly below is the case split on
`z <= 2 (sieveQ ε x) / x^(11/20+ε)` together with one monotonicity step for the constant, and it leaves
no goal open.

Both leaves are refuted, not open, and this is why they carry no proof. A single family of
coefficients defeats both cells: take `v0 = 0`, `E` empty, and `b0 x m = (-1) ^ (m / Q)` on the
short interval with `Q = sieveQ ε x`. Its divisor bound and its centred character prefix bound both
hold, the parities of consecutive blocks of length `Q` cancel in a prefix, and only the two partial
blocks survive, so a window sum is of size `Q` rather than of size `Q` times the logarithm saving
that the right-hand side `C (q Q)^2 x^(11/20+ε) (log x)^(-A)` allows. A direct count over the
window, averaged over the position of the window in the block, gives a mean square of
`0.47 Q^2` at `z = Q / x^(11/20+ε)` and `0.42 Q^2` at `z = 4 Q / x^(11/20+ε)`, hence a `y`-integral
of `1.2 Q^2 x^(11/20+ε)` and `1.0 Q^2 x^(11/20+ε)` against a budget of `C Q^2 x^(11/20+ε)`
divided by `(log x)^A`, which no single `C` meets for every large `x` and every `A`. The missing
input is a mean-square bound on the coefficient family itself, which the hypotheses of the target
do not supply: `hchar` controls prefixes only, and the divisor bound controls `b0` pointwise only.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_exceptional_set_moment_narrow

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF 1 of 2. Step: the lower cell of the short shift, `z <= 2 (sieveQ ε x) / x^(11/20+ε)`.
There the window is at most six sieve cutoffs long, so it meets the coefficient family through one
stretch of consecutive integers of that size, and the centred window sum is controlled without any
cancellation across cutoffs.

This is the target cut at `2 (sieveQ ε x) / x^(11/20+ε)`: it keeps the set `E` and its cardinality
bound as a hypothesis and says nothing above the cut, so it is strictly easier than the target and does
not assume it. Not vacuous: the empty set satisfies the cardinality hypothesis, `q = 1` is available,
and `z = sieveQ ε x / x^(11/20+ε)` lies between the lower limit and the cut. Refuted as cut, see the
file header. -/
theorem leaf_narrow_small_modulus_very_short_shift
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
          z ≤ 2 * sieveQ ε x / x ^ (11 / 20 + ε) →
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

/-- LEAF 2 of 2. Step: the upper cell of the short shift, `2 (sieveQ ε x) / x^(11/20+ε) <= z`,
still inside `z <= 1/2`. There the window spans between two and thirty-six sieve cutoffs, so the bound
is taken across blocks of the coefficient family, where consecutive blocks cancel in pairs and only
their ends survive.

This is the target cut at `2 (sieveQ ε x) / x^(11/20+ε)`: it keeps `E` and its cardinality bound as a
hypothesis and says nothing below the cut, so it is strictly easier than the target. Not vacuous:
`q = 2` with `sieveQ ε x >= 2` is available and `z = 4 (sieveQ ε x) / x^(11/20+ε)` lies between the
cut and the upper limit. Refuted as cut, see the file header. -/
theorem leaf_narrow_small_modulus_moderate_shift
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
  sorry

/-- The target statement, assembled from the two cells of the shift range with no sorry. The
constant is `|C₁| + |C₂| + 2`, which dominates both cell constants and keeps the logarithm positive;
the case split on `z <= 2 (sieveQ ε x) / x^(11/20+ε)` sends every admissible shift to the cell that
covers it, and one monotonicity step moves the constant of that cell up to the common one. No step
uses the target theorem. -/
theorem leaf_narrow_small_modulus_short_shift_split
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
  intro A hA
  obtain ⟨C₁, hC₁⟩ :=
    leaf_narrow_small_modulus_very_short_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₂, hC₂⟩ :=
    leaf_narrow_small_modulus_moderate_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  refine ⟨|C₁| + |C₂| + 2, ?_⟩
  intro x hx q hq hqQ hq2 z hzlo hzup hz12
  have hC₁x : C₁ ≤ x := by linarith [le_abs_self C₁, abs_nonneg C₂]
  have hC₂x : C₂ ≤ x := by linarith [le_abs_self C₂, abs_nonneg C₁]
  have hx2 : (2 : ℝ) ≤ x := by linarith [abs_nonneg C₁, abs_nonneg C₂]
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
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
  by_cases hzs : z ≤ 2 * sieveQ ε x / x ^ (11 / 20 + ε)
  · exact le_trans
      (hC₁ x hC₁x q hq hqQ hq2 z hzlo hzup hzs hz12)
      (hmono C₁ (|C₁| + |C₂| + 2) hC₁m)
  · exact le_trans
      (hC₂ x hC₂x q hq hqQ hq2 z hzlo hzup (le_of_lt (lt_of_not_ge hzs)) hz12)
      (hmono C₂ (|C₁| + |C₂| + 2) hC₂m)
