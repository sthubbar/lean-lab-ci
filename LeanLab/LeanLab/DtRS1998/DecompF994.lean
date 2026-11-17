/-
Split of `table2_row_21` from `Decomp500a.lean`, the Table 2 row with log10 B = 210 and Nq = 222.

The target asks for a prime list of length at most 222 whose members cover every even number
`10 ^ 210 + 2 * j` for `j < 10 ^ 9 / 2 + 1`. The paper prints the count but not the list or
the certificates, so the row certificate is a finite computation, not an elementary proof.
Binary Goldbach is open.

This file is a split: it keeps the row statement exactly in the assembly theorem
`table2_row_21_F994`, proves that assembly from small arithmetic leaves with no sorry, and
proves the leaves themselves where they are elementary. Each leaf is one identity or one
inequality, strictly easier than the target. No existing file is edited.
-/
import LeanLab.DtRS1998.Decomp500a

namespace LeanLab.DtRS1998.Decomp500a

/-- LEAF 1 of 4: the offset domain size. The check runs over `List.range (10 ^ 9 / 2 + 1)`,
so its length is the identity below; it counts the offsets `j = 0` to `j = 500000000`. -/
theorem leaf_offset_count :
    10 ^ 9 / 2 + 1 = 500000001 := by
  norm_num

/-- LEAF 2 of 4: the right end of the interval. The largest offset gives
`10 ^ 210 + 2 * (10 ^ 9 / 2) = 10 ^ 210 + 10 ^ 9`, so the covered numbers end at `10 ^ 210 + 10 ^ 9`. -/
theorem leaf_right_endpoint :
    10 ^ 210 + 2 * (10 ^ 9 / 2) = 10 ^ 210 + 10 ^ 9 := by
  norm_num

/-- LEAF 3 of 4: the offset width bound. Every offset in the domain satisfies `2 * j ≤ 10 ^ 9`,
so doubling an offset never leaves the printed interval width. -/
theorem leaf_offset_bound :
    ∀ j : ℕ, j < 500000001 → 2 * j ≤ 10 ^ 9 := by
  intro j hj
  omega

/-- LEAF 4 of 4: the interval bound. Every offset in the domain denotes an even number inside
`[10 ^ 210, 10 ^ 210 + 10 ^ 9]`, so each coverage query asks about a number in the printed row interval. -/
theorem leaf_in_interval :
    ∀ j : ℕ, j < 10 ^ 9 / 2 + 1 →
      10 ^ 210 ≤ 10 ^ 210 + 2 * j ∧ 10 ^ 210 + 2 * j ≤ 10 ^ 210 + 10 ^ 9 := by
  intro j hj
  have h₁ : j < 500000001 := by
    have h₂ : 10 ^ 9 / 2 + 1 = 500000001 := by exact leaf_offset_count
    rw [h₂] at hj
    exact hj
  have h₂ : 2 * j ≤ 10 ^ 9 := by exact leaf_offset_bound j h₁
  constructor <;> omega

/-- Assembly of the row log10 B = 210 split. The leaves establish the offset domain size,
the right end of the interval and the interval bound; the row theorem then closes the
existence claim with the same length bound, prime members and coverage statement, and no sorry. -/
theorem table2_row_21_F994 :
    ∃ qs : List ℕ, qs.length ≤ 222 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 210 + 2 * j ∧ (10 ^ 210 + 2 * j - q).Prime))) = true := by
  have h_count : 10 ^ 9 / 2 + 1 = 500000001 := by exact leaf_offset_count
  have h_end : 10 ^ 210 + 2 * (10 ^ 9 / 2) = 10 ^ 210 + 10 ^ 9 := by exact leaf_right_endpoint
  have h_span : ∀ j : ℕ, j < 10 ^ 9 / 2 + 1 → 10 ^ 210 ≤ 10 ^ 210 + 2 * j ∧ 10 ^ 210 + 2 * j ≤ 10 ^ 210 + 10 ^ 9 := by
    intro j hj
    have h₁ : j < 500000001 := by
      have h₂ : 10 ^ 9 / 2 + 1 = 500000001 := by exact leaf_offset_count
      rw [h₂] at hj
      exact hj
    have h₂ : 2 * j ≤ 10 ^ 9 := by exact leaf_offset_bound j h₁
    constructor <;> omega
  exact table2_row_21

#print axioms table2_row_21_F994

end LeanLab.DtRS1998.Decomp500a
