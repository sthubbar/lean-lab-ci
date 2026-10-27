/-
P0030 Goldston 1990 pages 288 and 289, the unweighted pair counts in Lemma 1.
The sum count is stated for n at least 1 to avoid a negative integer n minus 1 at zero.
The difference count uses natural subtraction for the nonnegative part.
AI wrote the Lean code. Goldbach is open. Known mathematics.
-/
import Mathlib

namespace LeanLab.GoldbachGaps.MainLemmaCounts
open Finset

/-- The ordered sum pairs in the interval from 1 to N have a triangular count. -/
theorem sum_pair_count (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ 2 * N) :
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun p : ℕ × ℕ => p.1 + p.2 = n).card =
      min (n - 1) (2 * N - n + 1) := by
  have heq : ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p : ℕ × ℕ => p.1 + p.2 = n) =
      (Icc (max 1 (n - N)) (min N (n - 1))).image (fun k : ℕ => (k, n - k)) := by
    ext p
    simp only [mem_filter, mem_product, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hp1, hp2⟩, hsum⟩
      refine ⟨p.1, ⟨by omega, by omega⟩, ?_⟩
      exact Prod.ext rfl (by omega)
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      dsimp
      omega
  rw [heq, Finset.card_image_of_injective _ (fun a b he => (Prod.mk.inj he).1), Nat.card_Icc]
  omega

/-- The ordered pairs of difference n have count max of N minus n and zero. -/
theorem difference_pair_count (N n : ℕ) :
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun p : ℕ × ℕ => p.1 = p.2 + n).card = N - n := by
  have heq : ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p : ℕ × ℕ => p.1 = p.2 + n) =
      (Icc 1 (N - n)).image (fun k : ℕ => (k + n, k)) := by
    ext p
    simp only [mem_filter, mem_product, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hp1, hp2⟩, hsum⟩
      exact ⟨p.2, ⟨by omega, by omega⟩, Prod.ext (by omega) rfl⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      dsimp
      omega
  rw [heq, Finset.card_image_of_injective _ (fun a b he => (Prod.mk.inj he).2), Nat.card_Icc]
  omega

end LeanLab.GoldbachGaps.MainLemmaCounts
