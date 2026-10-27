import Mathlib
import LeanLab.GoldbachAverage.OddSum
import LeanLab.GoldbachAverage.OddSumPNT

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace LeanLab.GoldbachAverage.Triad13

theorem triad13_main (n : ℕ) (hn : Odd n) :
    G n = 2 * ∑ j ∈ Icc 1 (Nat.log 2 n), Real.log 2 * Λ (n - 2 ^ j) := by
  rw [G_odd_eq n hn]
  congr 1
  have h1 : ∑ a ∈ range (n + 1), fE a * fO (n - a) = ∑ a ∈ range (n + 1), fE a * Λ (n - a) := by
    apply sum_congr rfl
    intro a ha
    unfold fE fO
    split_ifs with he he2
    · exfalso
      rw [mem_range] at ha
      have : Odd (n - a) := by
        obtain ⟨k, hk⟩ := hn; obtain ⟨l, hl⟩ := he
        use k - l; omega
      exact Nat.not_even_iff_odd.2 this he2
    · rfl
    · rw [zero_mul, zero_mul]
    · rfl
  rw [h1]
  exact sum_fE_mul n (fun a => Λ (n - a))
