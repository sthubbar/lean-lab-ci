/-
Split of the leaf `leaf_mvt_threshold` of `LeanLab.ExceptionalSet.SPLIT_leaf_karLemma1_mvt`:
the instance of Vinogradov's mean value theorem at the least admissible exponent
`b = n l + [n(n+1)/4 + 1]`, for every `n >= 12`, `l > 0` and `P > 0`.

The cut is the standard one for a mean value bound.  The integrand of the target is the
`2b`-th power of a modulus, so the integral is a count: expanding the modulus and
integrating the exponential over the cube leaves exactly the number of `2b`-tuples
`(x_1, ..., x_b, y_1, ..., y_b)` in `[1, P]` whose first `n` power sums agree.  The
target's exponent is written as `(diagonal power) times (excess factor)`,
`P^(2b - n(n+1)/2) * P^(n(n+1)/2 * (1 - 1/n)^l)`, so the bound on the count and the
reassembly of that product are separated.  The count bound itself is cut at `l = 1`,
where the elementary determination of a tuple by its power sums already suffices, and at
`l >= 2`, where the mean value input proper is needed.

AI wrote the Lean code.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_karLemma1_mvt

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

open Classical

/-! ### Leaves -/

/-- LEAF. The identity that turns the target into a count: the modulus is expanded and the
exponential integrated out over the unit cube, so the integral of the `2b`-th power of the
exponential sum, at the target's exponent `b = n l + [n(n+1)/4 + 1]`, equals the number of
pairs of `b`-tuples `(x, y)` with entries in `[1, P]` whose power sums
`x_1^j + ... + x_b^j` and `y_1^j + ... + y_b^j` agree for every `j` from `1` to `n`.
One identity, no inequality. -/
theorem leaf_integral_eq_solution_count :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℕ)
      = ∑ x : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0) := by
  sorry

/-- LEAF. The threshold exponent bound at `l = 1`, in counting form and with the diagonal
power taken out: at `b = n + [n(n+1)/4 + 1]` the number of pairs of `b`-tuples in `[1, P]`
with equal power sums up to order `n` is below `(20 n)^(n(n+1)/2)` times
`P^(n(n+1)/2 * (1 - 1/n))` times `P^(2b - n(n+1)/2)`. One inequality, the `l = 1` instance
only, the case the elementary determination of a tuple by its first `n` power sums reaches;
the number of `b`-tuples above `n` carrying a fixed initial data is what is being counted. -/
theorem leaf_solution_count_at_one :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, l = 1 → ∀ P : ℕ, 0 < P →
      ∑ x : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
      < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) *
             (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  sorry

/-- LEAF. The same threshold bound for `l ≥ 2`, in the same counting form. This is the
step that needs genuine mean value input rather than the elementary determination count:
`b` exceeds `n + [n(n+1)/4 + 1]`, so each initial segment of a tuple is determined by its
power sums only up to `n` entries and the count must be fed through the mean value
inequality at the previous exponent. One inequality. -/
theorem leaf_solution_count_deep :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → 2 ≤ l → ∀ P : ℕ, 0 < P →
      ∑ x : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
      < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) *
             (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  sorry

/-- LEAF. The bookkeeping identity that reassembles the two factors: for `P > 0` the
product of the diagonal power `P^(2b - n(n+1)/2)` and the excess factor
`P^(n(n+1)/2 * (1 - 1/n)^l)` is the single power of `P` at the sum of the two exponents,
with the constant `(20 n)^(n(n+1)/2 * l)` carried along. One identity. -/
theorem leaf_excess_exponent_identity :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) *
             (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))
      = (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  intro n hn l hl P hP
  have hp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [Real.rpow_add hp]
  ring

/-! ### Assembly -/

/-- The sealed statement of the target `leaf_mvt_threshold`, from the four leaves of this
file: the integral is the count, the count is bounded at `l = 1` and at `l ≥ 2`, and the
two factors of the bound multiply back to the single power at the target's exponent. -/
theorem leaf_mvt_threshold_split :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℕ) <
        (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  intro n hn l hl P hP
  rcases Nat.lt_or_ge l 2 with hsmall | hbig
  · have hl1 : l = 1 := by omega
    rw [leaf_integral_eq_solution_count n hn l hl P hP,
      ← leaf_excess_exponent_identity n hn l hl P hP]
    exact leaf_solution_count_at_one n hn l hl1 P hP
  · rw [leaf_integral_eq_solution_count n hn l hl P hP,
      ← leaf_excess_exponent_identity n hn l hl P hP]
    exact leaf_solution_count_deep n hn l hl hbig P hP

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
