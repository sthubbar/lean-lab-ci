/-
P0005 Section 1.3 on page 2041: disjoint blocks and the even-number count used in screening.
The counts here follow by an interval bijection, with no large finite enumeration.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.BlockFormatTask72

namespace LeanLab.Verifications.BlockCountsTask72

/-- The even integers in the paper's kth block. -/
def blockEvens (k : ℕ) : Finset ℕ :=
  (Finset.Ioc (max 4 (10 ^ 12 * k)) (10 ^ 12 * (k + 1))).filter Even

/-- Disjointness of the published blocks. -/
theorem block_unique {j k n : ℕ}
    (hjlo : max 4 (10 ^ 12 * j) < n) (hjhi : n ≤ 10 ^ 12 * (j + 1))
    (hklo : max 4 (10 ^ 12 * k) < n) (hkhi : n ≤ 10 ^ 12 * (k + 1)) : j = k := by
  norm_num at *
  omega

/-- Doubling maps a half-length interval exactly onto the even numbers in a block. -/
theorem blockEvens_image (k : ℕ) :
    blockEvens k = (Finset.Ioc (max 2 (500000000000 * k))
      (500000000000 * (k + 1))).image (fun m => 2 * m) := by
  ext n
  simp only [blockEvens, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hnlo, hnhi⟩, ⟨m, hm⟩⟩
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩ <;> norm_num at * <;> omega
  · rintro ⟨m, ⟨hmlo, hmhi⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ⟨m, by omega⟩⟩ <;> norm_num at * <;> omega

/-- A symbolic count of the even numbers in any block. -/
theorem blockEvens_card (k : ℕ) :
    (blockEvens k).card = 500000000000 * (k + 1) - max 2 (500000000000 * k) := by
  rw [blockEvens_image, Finset.card_image_of_injective _ (by
    intro a b hab
    exact mul_left_cancel₀ (by decide : (2 : ℕ) ≠ 0) hab)]
  exact Nat.card_Ioc _ _

/-- The first block excludes the even integers two and four. -/
theorem first_block_card : (blockEvens 0).card = 499999999998 := by
  rw [blockEvens_card]
  norm_num

/-- Every positive-index block has exactly half a trillion even numbers. -/
theorem positive_block_card {k : ℕ} (hk : 0 < k) :
    (blockEvens k).card = 500000000000 := by
  rw [blockEvens_card]
  omega

open scoped BigOperators

/-- The first N plus one blocks have a symbolic total even-number count. -/
theorem sum_block_card (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (blockEvens k).card) =
      (N + 1) * 500000000000 - 2 := by
  have h : ∀ k : ℕ, (blockEvens (k + 1)).card = 500000000000 :=
    fun k => positive_block_card (by omega)
  rw [Finset.sum_range_succ']
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_range, first_block_card]
  simp only [nsmul_eq_mul, Nat.cast_id]
  omega

/-- The four million blocks contain exactly two quintillion minus two even integers. -/
theorem total_block_card :
    (∑ k ∈ Finset.range (4 * 10 ^ 6), (blockEvens k).card) = 1999999999999999998 :=
  sum_block_card 3999999

end LeanLab.Verifications.BlockCountsTask72
