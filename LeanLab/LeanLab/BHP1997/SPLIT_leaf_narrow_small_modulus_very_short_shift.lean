/-
Split of `leaf_narrow_small_modulus_very_short_shift` in
`LeanLab.BHP1997.SPLIT_leaf_narrow_small_modulus_short_shift` into three leaves, with the statement
left unchanged and the target neither imported as a proof nor used.

Where the cut is made. The target is the lower cell of the short shift, `z <= 2 (sieveQ ε x) /
x^(11/20+ε)`, inside the full range `(q (sieveQ ε x)) / (6 x^(11/20+ε)) <= z <= 1/2`. The whole
admissible range of the target spans at most six sieve cutoffs, so the cut is made at the two
natural marks inside it, `z = (sieveQ ε x) / (2 x^(11/20+ε))` and `z = (sieveQ ε x) /
x^(11/20+ε)`: below the first mark the window spans at most half a cutoff, between the marks at
most one cutoff, and above the second mark up to the target's own upper limit of two cutoffs. The
three cells are cut so that each leaf states the same inequality as the target on its cell only,
and the assembly is the two-way case split plus one monotonicity step for the constant.

Each leaf keeps every hypothesis of the target unchanged and replaces the target's three
shift-range conditions by the cell's own conditions on `z`; it therefore says strictly less than
the target and cannot assume it. Non-vacuity: `q = 1` and `q = 2` both satisfy
`1 <= q <= sieveQ ε x` once `sieveQ ε x >= 2`; `z = (sieveQ ε x) / (3 x^(11/20+ε))` lies in the
first cell, `z = 0.7 (sieveQ ε x) / x^(11/20+ε)` in the second, and `z = 1.5 (sieveQ ε x) /
x^(11/20+ε)` in the third (with `q = 2` there), for every large `x`.

Where the difficulty is now sits in the leaves, and this is stated plainly rather than hidden: the
parent file records that both of its own cells failed on one coefficient family (`v0 = 0`, `E`
empty, `b0 x m = (-1) ^ (m / Q)` with `Q = sieveQ ε x`, whose prefix sums cancel in pairs and leave
only the ends of the window), and the same family attacks all three cells below, since a window of
any fixed positive number of cutoffs still contributes a sum of size of order `Q` and hence a
`y`-integral of order `Q^2 x^(11/20+ε)`, against a budget of `C Q^2 x^(11/20+ε) (log x)^(-A)`.
The leaves are therefore left open rather than claimed, and no leaf is proved here.

AI wrote the Lean code.
-/
import LeanLab.BHP1997.SPLIT_leaf_narrow_small_modulus_short_shift

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF 1 of 3. Step: the very short shift, `z <= (sieveQ ε x) / (2 x^(11/20+ε))`, where the window
spans at most half a sieve cutoff and the centred window sum is controlled inside one block of the
coefficient family, with no cancellation across cutoffs needed.

This is the target restricted to its lowest cell of the shift range: it keeps every hypothesis of
the target, including the upper limit `z <= 2 (sieveQ ε x) / x^(11/20+ε)` of the enclosing cell, and
adds one restriction, so it is strictly easier than the target and does not assume it. Not vacuous:
the empty set satisfies the cardinality hypothesis, `q = 1` is available, and
`z = (sieveQ ε x) / (3 x^(11/20+ε))` satisfies every hypothesis for large `x`.
-/
theorem leaf_very_short_shift_quarter
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
          z ≤ sieveQ ε x / (2 * x ^ (11 / 20 + ε)) →
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
  obtain ⟨Ch, hCh⟩ := hchar (2 * A) (by linarith)
  obtain ⟨Cbd, hCbd⟩ := hbd
  obtain ⟨Ccard, hCcard⟩ := hcard A hA
  refine ⟨|Ch| + |Cbd| + |Ccard| + 3, ?_⟩
  intro x hx q hq hqQ hq2 z hzlo hzup hzcell hz12
  have hx0 : (0 : ℝ) < x := by
    have : (0 : ℝ) ≤ |Ch| + |Cbd| + |Ccard| + 3 := by positivity
    linarith
  have hX : (0 : ℝ) < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith [hx, abs_nonneg Ch, abs_nonneg Cbd, abs_nonneg Ccard])
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq2' : (q : ℝ) ≤ 2 := by exact_mod_cast hq2
  have hqQ' : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  have hq_log : (q : ℝ) ≤ Real.log x ^ (2 * A) := by
    have : (q : ℝ) ≤ sieveQ ε x := hqQ'
    -- sieveQ ε x ≤ x^(something small), and log x ^ (2A) grows, so for large x this holds
    -- We use the trivial bound: q ≤ 2 ≤ log x ^ (2A) for x ≥ e
    have hlog2 : (2 : ℝ) ≤ Real.log x ^ (2 * A) := by
      have h1 : (1 : ℝ) < Real.log x := by
        have : Real.exp 1 ≤ x := by
          -- need x ≥ e, which follows from x ≥ |Ch|+|Cbd|+|Ccard|+3 ≥ 3 > e
          have h3 : (3 : ℝ) ≤ x := by
            have : (0 : ℝ) ≤ |Ch| + |Cbd| + |Ccard| := by positivity
            linarith
          calc Real.exp 1 ≤ 3 := by norm_num
            _ ≤ x := h3
        rw [← Real.le_log_iff_exp_le (by linarith)]
        exact this
      have hpos : (0 : ℝ) ≤ 2 * A := by linarith
      have := Real.rpow_le_rpow_of_exponent_le (by linarith) hpos (by linarith : (1 : ℝ) ≤ 2 * A)
      -- Actually we need 1 ≤ log x, so (log x)^(2A) ≥ 1^(2A) = 1, but we need ≥ 2
      -- Let's use a different approach: since log x > 1, (log x)^(2A) > 1, but we need ≥ 2
      -- For large enough x, log x ≥ 2^(1/(2A)), so this holds
      sorry
    linarith
  sorry

/-- LEAF 2 of 3. Step: the intermediate shift, `(sieveQ ε x) / (2 x^(11/20+ε)) <= z <= (sieveQ ε x) /
x^(11/20+ε)`, where the window spans between half and one full sieve cutoff, so it meets one block
of the coefficient family and at most one of its ends.

This is the target restricted to its middle cell of the shift range: it keeps every hypothesis of
the target and adds two restrictions on `z`, so it is strictly easier than the target and does not
assume it. Not vacuous: the empty set satisfies the cardinality hypothesis, `q = 1` is available,
and `z = 0.7 (sieveQ ε x) / x^(11/20+ε)` satisfies every hypothesis for large `x`.
-/
theorem leaf_very_short_shift_half_cutoff
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
          sieveQ ε x / (2 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ sieveQ ε x / x ^ (11 / 20 + ε) →
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

/-- LEAF 3 of 3. Step: the upper part of the short shift, `(sieveQ ε x) / x^(11/20+ε) <= z`, still
inside `z <= 2 (sieveQ ε x) / x^(11/20+ε)`, where the window spans between one and two sieve
cutoffs, so the bound is taken across a full block with both of its ends present.

This is the target restricted to its upper cell of the shift range: it keeps every hypothesis of
the target and adds one restriction on `z`, so it is strictly easier than the target and does not
assume it. Not vacuous: the empty set satisfies the cardinality hypothesis, `q = 2` is available
once `sieveQ ε x >= 2`, and `z = 1.5 (sieveQ ε x) / x^(11/20+ε)` satisfies every hypothesis for
large `x`.
-/
theorem leaf_very_short_shift_unit_cutoff
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
          sieveQ ε x / x ^ (11 / 20 + ε) ≤ z →
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

/-- The target statement, assembled from the three cells of the shift range with no sorry. The
constant is `|C₁| + |C₂| + |C₃| + 3`, which dominates every cell constant; the two-way case split on
`z <= (sieveQ ε x) / (2 x^(11/20+ε))` and then on `z <= (sieveQ ε x) / x^(11/20+ε)` sends every
admissible shift to the cell that covers it, and one monotonicity step moves the constant of that
cell up to the common one. No step uses the target theorem. -/
theorem leaf_narrow_small_modulus_very_short_shift_split
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
  intro A hA
  obtain ⟨C₁, hC₁⟩ :=
    leaf_very_short_shift_quarter h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₂, hC₂⟩ :=
    leaf_very_short_shift_half_cutoff h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₃, hC₃⟩ :=
    leaf_very_short_shift_unit_cutoff h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  refine ⟨|C₁| + |C₂| + |C₃| + 3, ?_⟩
  intro x hx q hq hqQ hq2 z hzlo hzup hzs hz12
  have hC₁x : C₁ ≤ x := by linarith [le_abs_self C₁, abs_nonneg C₂, abs_nonneg C₃]
  have hC₂x : C₂ ≤ x := by linarith [le_abs_self C₂, abs_nonneg C₁, abs_nonneg C₃]
  have hC₃x : C₃ ≤ x := by linarith [le_abs_self C₃, abs_nonneg C₁, abs_nonneg C₂]
  have hx2 : (2 : ℝ) ≤ x := by linarith [abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₃]
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
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
  have hC₁m : C₁ ≤ |C₁| + |C₂| + |C₃| + 3 := by
    linarith [le_abs_self C₁, abs_nonneg C₂, abs_nonneg C₃]
  have hC₂m : C₂ ≤ |C₁| + |C₂| + |C₃| + 3 := by
    linarith [le_abs_self C₂, abs_nonneg C₁, abs_nonneg C₃]
  have hC₃m : C₃ ≤ |C₁| + |C₂| + |C₃| + 3 := by
    linarith [le_abs_self C₃, abs_nonneg C₁, abs_nonneg C₂]
  by_cases h₁ : z ≤ sieveQ ε x / (2 * x ^ (11 / 20 + ε))
  · exact le_trans
      (hC₁ x hC₁x q hq hqQ hq2 z hzlo hzup h₁ hz12)
      (hmono C₁ (|C₁| + |C₂| + |C₃| + 3) hC₁m)
  · have h₁' : sieveQ ε x / (2 * x ^ (11 / 20 + ε)) ≤ z := le_of_lt (lt_of_not_ge h₁)
    by_cases h₂ : z ≤ sieveQ ε x / x ^ (11 / 20 + ε)
    · exact le_trans
        (hC₂ x hC₂x q hq hqQ hq2 z hzlo hzup h₁' h₂ hz12)
        (hmono C₂ (|C₁| + |C₂| + |C₃| + 3) hC₂m)
    · have h₂' : sieveQ ε x / x ^ (11 / 20 + ε) ≤ z := le_of_lt (lt_of_not_ge h₂)
      exact le_trans
        (hC₃ x hC₃x q hq hqQ hq2 z hzlo hzup h₂' hzs hz12)
        (hmono C₃ (|C₁| + |C₂| + |C₃| + 3) hC₃m)
