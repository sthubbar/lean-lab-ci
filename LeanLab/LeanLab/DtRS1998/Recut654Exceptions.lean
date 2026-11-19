/-
AI wrote this Lean code for CODEX task654b.
P0037 pages 210 and 212, shifted sieve with separately checked exceptional indices.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Exceptions

open LeanLab.Verifications.Top50.Bits

/-- A shifted sieve and explicit prime companions at its missing bits cover a window. -/
theorem prime_differences_of_bitmap_patches {A count lo W : ℕ} (ss ks : List ℕ)
    (h2 : 2 ≤ lo) (hW : lo + W ≤ B2) (hA : lo ≤ A)
    (patch : ∀ k ∈ ks, ∃ s ∈ ss, s ≤ lo + k ∧ (lo + k - s).Prime)
    (h : wem lo A (A + 2 * (count - 1)) &&&
      (gm (wpm2 lo W) ss ||| gm 1 ks) = wem lo A (A + 2 * (count - 1))) :
    ∀ t : ℕ, t < count →
      ∃ s ∈ ss, s ≤ A + 2 * t ∧ (A + 2 * t - s).Prime := by
  intro t ht
  have hbit := testBit_wem (lo := lo) (A := A) (B := A + 2 * (count - 1))
    (n := A + 2 * t) hA (by omega) (by omega) (by simp)
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at hbit
  rw [Nat.testBit_or, Bool.or_eq_true] at hbit
  rcases hbit.2 with hb | hb
  · obtain ⟨s, hs, hsn, hp⟩ := of_gm _ ss (A + 2 * t - lo) hb
    refine ⟨s, hs, by omega, ?_⟩
    have hprime := prime_of_wpm2 h2 hW hp
    convert hprime using 1 <;> omega
  · obtain ⟨k, hk, hkn, hp⟩ := of_gm 1 ks (A + 2 * t - lo) hb
    have hz := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hp
    have he : lo + k = A + 2 * t := by omega
    simpa only [he] using patch k hk

/-- A one-bit sieve certifies an individual small companion prime. -/
theorem prime_of_bit (n : ℕ) (h2 : 2 ≤ n) (hn : n + 1 ≤ B2)
    (h : (wpm2 n 1).testBit 0 = true) : n.Prime := by
  simpa using prime_of_wpm2 (lo := n) (W := 1) (i := 0) h2 hn h

end LeanLab.DtRS1998.Recut654Exceptions
