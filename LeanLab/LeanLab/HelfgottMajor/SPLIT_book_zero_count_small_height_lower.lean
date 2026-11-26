import LeanLab.HelfgottMajor.ZeroCount1623

/-!
# Split of `book_zero_count_small_height_lower`

The leaf `book_zero_count_small_height_lower` of `SPLIT_book_zero_count_small_height` is the lower
direction `bookMain q T - bookCount χ T ≤ bookError q T` on `1 ≤ T ≤ 2`, `2πe ≤ q T`. On main it is
discharged only by calling the target `book_zero_count`, so it carries no progress of its own.
This file gives a non-circular split.

* Proved here, no input: when `log (q T) ≤ 21` the main term alone is at most the error. Indeed
  `T / (2π) ≤ 1 / π < 0.3184` and `log (q T / (2πe)) ≤ log (q T) - 1`, so the main term is at most
  `0.3184 * 20 = 6.37`, while the error is at least `0.15 * log (q T) + 3.389`; the inequality
  `0.3184 (L - 1) ≤ 0.15 L + 3.389` holds for all `L ≤ 22.01`. Since the count is nonnegative the
  lower direction follows. This covers every modulus `q ≤ e ^ 21 / 2`, about `6.59 * 10 ^ 8`.
* One LEAF remains, `log (q T) > 21`: the book estimate display 3.95, lower side, for the very
  large conductors, where the main term really exceeds the error and a zero count from below is
  needed.

This file imports only `ZeroCount1623`, since `SPLIT_book_zero_count_small_height` had no built
olean when it was written; the statement of `book_zero_count_small_height_lower_split` is
character for character that of `book_zero_count_small_height_lower`, so the import can be
switched to that file without change.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- Arithmetic part, proved: on `1 ≤ T ≤ 2` with `2πe ≤ q T` and `log (q T) ≤ 21`, the main term
is at most the error. -/
theorem bookMain_le_bookError_small_height_of_log_le {T : ℝ} (hT : 1 ≤ T) (hT2 : T ≤ 2)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T)
    (hlog : Real.log ((q : ℝ) * T) ≤ 21) :
    bookMain q T ≤ bookError q T := by
  have hpi := Real.pi_gt_d4
  have hpos : 0 < (q : ℝ) * T := lt_of_lt_of_le (by positivity) hmain
  have hcpos : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  have hsplit : Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) =
      Real.log ((q : ℝ) * T) - Real.log (2 * Real.pi) - 1 := by
    rw [Real.log_div hpos.ne' hcpos.ne', Real.log_mul (by positivity) (Real.exp_pos 1).ne',
      Real.log_exp]
    ring
  have h2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have hge : 0 ≤ Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) :=
    Real.log_nonneg ((one_le_div hcpos).mpr hmain)
  set M := Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) with hM
  set Lg := Real.log ((q : ℝ) * T) with hLg
  have hML : M ≤ Lg - 1 := by rw [hsplit]; linarith
  have hfac : T / (2 * Real.pi) ≤ 0.3184 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hfac0 : 0 ≤ T / (2 * Real.pi) := by positivity
  unfold bookMain bookError
  rw [← hM, ← hLg]
  calc T / (2 * Real.pi) * M ≤ 0.3184 * M := mul_le_mul_of_nonneg_right hfac hge
    _ ≤ 0.3184 * (Lg - 1) := by nlinarith
    _ ≤ 0.15 * Lg + 3.389 := by nlinarith

/- Numerical checks for the next LEAF. At `T = 1`, `q T = e ^ 21` the main term is `2.89` and
the error `6.54`, at `T = 2`, `q T = e ^ 21` they are `5.78` and `6.54`, so the leaf is slack at
its lower edge; at `T = 2`, `q = 10 ^ 30` it asks that at least `21.31 - 13.85 = 7.45` zeros, with
half weights, lie in `0 ≤ Im ρ ≤ 2`, against an expected `21.3`. The main term exceeds the error
at `T = 2` once `log (q T) > 25.5`, and at `T = 1` once `log (q T) > 417`. This is a lower bound
on a count, never an upper bound, so it is not a uniform bound on central multiplicity. -/

/-- LEAF: Helfgott, The ternary Goldbach problem, book display 3.95 as used on pages 431 and 432
in the proof of Lemma 16.9 with the error of display 16.21, after Rosser, McCurley Theorem 2.1
and Trudgian Theorem 1; lower side of the count at small height `1 ≤ T ≤ 2`, restricted to the
very large conductors `log (q T) > 21`. A genuine lower bound on the number of zeros with
`0 ≤ Im ρ ≤ T`, of order `T / (2π) log q`, from the argument principle with the Stirling
expansion of the gamma factor. Class HARD. -/
theorem book_zero_count_small_height_lower_large_conductor (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT2 : T ≤ 2)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T)
    (hlog : 21 < Real.log ((q : ℝ) * T)) :
    bookMain q T - bookCount χ T ≤ bookError q T := by
  have h : |bookCount χ T - bookMain q T| ≤ bookError q T := book_zero_count χ hχ hT
  linarith [abs_le.mp h]

/-- Assembly, with the same statement as `book_zero_count_small_height_lower`: below
`log (q T) = 21` the arithmetic part and the nonnegativity of the count, above it the leaf. -/
theorem book_zero_count_small_height_lower_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hT2 : T ≤ 2)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookMain q T - bookCount χ T ≤ bookError q T := by
  rcases le_or_gt (Real.log ((q : ℝ) * T)) 21 with hlog | hlog
  · have h1 := bookMain_le_bookError_small_height_of_log_le (q := q) hT hT2 hmain hlog
    have h2 : 0 ≤ bookCount χ T := by
      unfold bookCount
      refine Finset.sum_nonneg fun ρ _ => mul_nonneg ?_ (Nat.cast_nonneg _)
      unfold halfWeight
      split_ifs <;> norm_num
    linarith
  · exact book_zero_count_small_height_lower_large_conductor χ hχ hT hT2 hmain hlog

#print axioms book_zero_count_small_height_lower_split

end LeanLab.HelfgottMajor.ZeroCount1623
