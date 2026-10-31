import LeanLab.LZCesaroShort.Lemma8Proof

/-!
# R-5040, the Cesàro weighted Goldbach count as a ψ₁ convolution

Lab proof, route R-5040, unit U-5325, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known,
elementary, no cited input. `Σ_{n ≤ N} (N - n) R(n) = Σ_{a ≤ N} Λ(a) ψ₁(N - a)`, with
`R(n) = Σ_{a + b = n} Λ(a)Λ(b)` and `ψ₁(y) = Σ_{b ≤ y} Λ(b)(y - b)`: the first Cesàro moment of the
binary Goldbach count is one convolution of Λ with ψ₁, so the lab's explicit formula for ψ₁ turns
it into single and double sums over zeros. This is the smallest Lean lemma of route R-5040; it is
not progress on Goldbach, which is open.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.Routes.R5040

open LZCesaroShort

theorem cesaro_eq_conv (N : ℕ) :
    ∑ n ∈ range (N + 1), ((N : ℝ) - n) * R n =
      ∑ a ∈ range (N + 1), Λ a * Rg N ((N : ℝ) - a) := by
  -- both sides are the sum over `a + b ≤ N` of `Λ(a)Λ(b)(N - a - b)`
  have hL : ∑ n ∈ range (N + 1), ((N : ℝ) - n) * R n =
      ∑ n ∈ Ico 0 (N + 1), ∑ a ∈ Ico 0 (n + 1), ((N : ℝ) - n) * (Λ a * Λ (n - a)) := by
    rw [range_eq_Ico]
    apply sum_congr rfl; intro n _
    rw [R, Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Λ i * Λ j), mul_sum, range_eq_Ico]
  rw [hL, ← sum_Ico_Ico_comm, range_eq_Ico]
  apply sum_congr rfl; intro a ha
  rw [mem_Ico] at ha
  rw [Rg, mul_sum, sum_Ico_eq_sum_range]
  apply sum_subset_zero_on_sdiff (range_subset_range.mpr (by omega : N + 1 - a ≤ N + 1))
  · intro b hb
    rw [mem_sdiff, mem_range, mem_range] at hb
    have : (N : ℝ) - a - b ≤ 0 := by
      have : N + 1 - a ≤ b := not_lt.mp hb.2
      have : (N : ℝ) + 1 ≤ a + b := by
        have h' : N + 1 ≤ a + b := by omega
        exact_mod_cast h'
      linarith
    rw [max_eq_left this]; ring
  · intro b hb
    rw [mem_range] at hb
    have hab : a + b ≤ N := by omega
    have : 0 ≤ (N : ℝ) - a - b := by
      have : ((a + b : ℕ) : ℝ) ≤ N := by exact_mod_cast hab
      push_cast at this; linarith
    rw [max_eq_right this, show a + b - a = b by omega]
    push_cast; ring

end LeanLab.Routes.R5040
