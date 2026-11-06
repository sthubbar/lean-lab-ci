/-
P0042 page 423, the printed identity L of three and x equals pi of x minus three minus one.
Source https://ir.cwi.nl/pub/1570/1570D.pdf
The count uses even integers at least six, where the paper's odd-prime convention applies.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.GvLtR1989.PaperTables

namespace LeanLab.Verifications.CountThree397

open Finset

/-- P0042 page 423. The counted integers are three plus the odd primes through x minus three. -/
theorem three_partition_set (x : ℕ) :
    (range (x + 1)).filter (fun n => Even n ∧ 6 ≤ n ∧ minGB n = 3) =
      ((Nat.primesLE (x - 3)).erase 2).image (fun p => p + 3) := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨hn, he, h6, hm⟩ := mem_filter.mp hn
    have hp := (LeanLab.GvLtR1989.Paper.minGB_eq_three he h6).mp hm
    refine mem_image.mpr ⟨n - 3, mem_erase.mpr ⟨by omega, ?_⟩, by omega⟩
    exact Nat.mem_primesLE.mpr ⟨by have := mem_range.mp hn; omega, hp⟩
  · intro hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    obtain ⟨hne, hp⟩ := mem_erase.mp hp
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hp
    have h3 : 3 ≤ p := by have := hprime.two_le; omega
    have he : Even (p + 3) := by
      obtain ⟨k, hk⟩ := hprime.odd_of_ne_two hne
      exact ⟨k + 2, by omega⟩
    have h6 : 6 ≤ p + 3 := by omega
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), he, h6, ?_⟩
    exact (LeanLab.GvLtR1989.Paper.minGB_eq_three he h6).mpr (by simpa using hprime)

/-- P0042 page 423. The exact finite count is pi of x minus three minus one.
Natural subtraction also gives zero for x below six. -/
theorem three_partition_count (x : ℕ) :
    ((range (x + 1)).filter (fun n => Even n ∧ 6 ≤ n ∧ minGB n = 3)).card =
      Nat.primeCounting (x - 3) - 1 := by
  classical
  rw [three_partition_set, card_image_of_injective _ (by intro a b h; exact Nat.add_right_cancel h)]
  by_cases hx : 5 ≤ x
  · rw [card_erase_of_mem (Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩),
      Nat.primesLE_card_eq_primeCounting]
  · have hx3 : x - 3 ≤ 1 := by omega
    have hempty : Nat.primesLE (x - 3) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hle, hp⟩ := Nat.mem_primesLE.mp hp
      have := hp.two_le
      omega
    rw [hempty]
    simp only [erase_empty, card_empty]
    have hz : Nat.primeCounting (x - 3) = 0 := Nat.primeCounting_eq_zero_iff.mpr hx3
    rw [hz]

end LeanLab.Verifications.CountThree397
