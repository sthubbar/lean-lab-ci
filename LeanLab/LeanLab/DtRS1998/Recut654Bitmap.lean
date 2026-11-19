/-
AI wrote this Lean code for CODEX task654.
P0037 Section 4.2 page 210 and Section 5.2 page 212.
This transports the existing shifted sieve to small candidate displacements.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.Recut654Bitmap

open LeanLab.Verifications.Top50.Bits

/-- LEAF: The page 210 shifted sieve supplies prime differences for a finite block.
This implication is CONDITIONAL ON the displayed bitmap equality. -/
theorem prime_differences_of_bitmap {A count lo W : ℕ} (ss : List ℕ)
    (h2 : 2 ≤ lo) (hW : lo + W ≤ B2) (hA : lo ≤ A)
    (h : wem lo A (A + 2 * (count - 1)) &&& gm (wpm2 lo W) ss =
      wem lo A (A + 2 * (count - 1))) :
    ∀ t : ℕ, t < count →
      ∃ s ∈ ss, s ≤ A + 2 * t ∧ (A + 2 * t - s).Prime := by
  intro t ht
  have hbit := testBit_wem (lo := lo) (A := A) (B := A + 2 * (count - 1))
    (n := A + 2 * t) hA (by omega) (by omega) (by simp)
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at hbit
  obtain ⟨s, hs, hsn, hp⟩ := of_gm _ ss (A + 2 * t - lo) hbit.2
  refine ⟨s, hs, by omega, ?_⟩
  have hprime := prime_of_wpm2 h2 hW hp
  convert hprime using 1 <;> omega

end LeanLab.DtRS1998.Recut654Bitmap
