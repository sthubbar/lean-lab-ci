import LeanLab.HelfgottMajor.SPLIT_very_low_zero_count
import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Second split of `strip_count_at_one_le_explicit` in
`HelfgottMajor.SPLIT_very_low_zero_count`, route b.

The first split, `SPLIT_strip_count_at_one_le_explicit`, runs a rectangle contour and leaves
a border bound and a zero free border as leaves; the zero free border is not known for every
primitive character.  This route needs no new leaf: the count at height one is the two sided
closed count `ZeroCount1623.zero_count_two_sided` at `T = 1`, which is CONDITIONAL ON the one
cited input of the folder, `ZeroCount1623.book_zero_count`, the explicit zero count of
Rosser, McCurley Theorem 2.1 and Trudgian Theorem 1 in the one sided form of Helfgott's book,
display 3.95 used on pages 431 and 432 with error display 16.21.

At `T = 1` that count gives `(1 / π) log (q / (2 π e)) + 0.3 log q + 6.778`, and the target
keeps `0.5 log q + 17.7`, so the comparison is plain arithmetic with `log q ≥ 0`.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp389a

open Real

/-- The subtype sum of the multiplicities at height one is the finite sum over the strip
zeros at height one.  Proved, from `ZeroCount1623.tsum_zeroIdx`. -/
private lemma strip_tsum_one_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) =
    ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ 1).toFinset, (ZeroCount1623.mult χ ρ : ℝ) :=
  ZeroCount1623.tsum_zeroIdx χ 1 (fun z => (ZeroCount1623.mult χ z : ℝ))

/-- `strip_count_at_one_le_explicit`, CONDITIONAL ON `ZeroCount1623.book_zero_count` through
`ZeroCount1623.zero_count_two_sided` at height one. -/
theorem strip_count_at_one_le_explicit_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ≤
    (1 / π) * log (q / (2 * π * exp 1)) + 0.5 * log q + 17.7 := by
  rw [strip_tsum_one_eq q χ]
  have h := abs_le.mp (ZeroCount1623.zero_count_two_sided χ hχ (T := 1) le_rfl)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hlog : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hmain : 2 * ZeroCount1623.bookMain q 1 = (1 / π) * log (q / (2 * π * exp 1)) := by
    unfold ZeroCount1623.bookMain
    rw [mul_one]
    field_simp
  have herr : 2 * ZeroCount1623.bookError q 1 = 0.3 * log q + 6.778 := by
    unfold ZeroCount1623.bookError
    rw [mul_one]
    ring
  linarith [h.2]

end LeanLab.HelfgottMajor.Decomp389a
