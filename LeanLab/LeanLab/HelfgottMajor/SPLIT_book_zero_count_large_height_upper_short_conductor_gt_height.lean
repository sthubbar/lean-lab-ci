import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_short_conductor_le_height

/-!
# Split of `book_zero_count_large_height_upper_short_conductor_gt_height`

Same proof as for `q ≤ T`, from the leaves of
`SPLIT_book_zero_count_large_height_upper_short_conductor_le_height`: real characters from the
Bennett, Martin, O'Bryant and Rechnitzer two sided count, Math. Comp. 90 2021, Theorem 1.1, and the
conjugate symmetry, with the halved error fitting under the book error for every `q ≥ 2`; non real
characters from the one sided leaf. No new leaf.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- Split of `book_zero_count_large_height_upper_short_conductor_gt_height`, same statement. -/
theorem book_zero_count_large_height_upper_short_conductor_gt_height_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) {T : ℝ}
    (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20) (hTq : T < (q : ℝ))
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  by_cases hreal : χ⁻¹ = χ
  · exact book_upper_short_real_character χ hχ hreal hq2 hT2 hmain
  · exact book_one_sided_count_short_nonreal χ hχ hreal hq2 hT2 hT20 hmain

end LeanLab.HelfgottMajor.ZeroCount1623
