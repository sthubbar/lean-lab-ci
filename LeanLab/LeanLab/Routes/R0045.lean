import Mathlib

/-!
# R-0045, T3 MOONSHOT: arithmetic regularity and nilsequence obstructions for P + P

Unit U-1384, PC run 20261021T0903Z-24128. AI wrote the Lean code. Binary Goldbach is OPEN.
Nothing here is progress on Goldbach. Label KNOWN in substance: Green and Tao, Linear
equations in primes, exclude the binary problem as infinite complexity; Gowers and Wolf,
true complexity; Green and Tao, arithmetic regularity lemma.

Route: decompose the von Mangoldt function as structured nilsequence part plus small part
plus Gowers uniform part and count `r(N) = Σ_{a ≤ N} f(a) f(N - a)` from the structured part.
The lemmas below record why the uniform part cannot be discarded at a single `N`:
the only pointwise control is the `L²` bound `conv_le_sum_sq`, and it is attained by
sign patterns symmetric about `N/2` whose total sum, the averaged statistic, is zero.
-/

namespace LeanLab.Routes.R0045

open Finset

/-- The binary convolution at `N`. Plain math: `(f * f)(N) = Σ_{a=0}^{N} f(a) f(N - a)`. -/
def conv (f : ℕ → ℤ) (N : ℕ) : ℤ := ∑ a ∈ range (N + 1), f a * f (N - a)

/-- NEW. Pointwise `L²` bound, the only control a single `N` admits.
Plain math: `(f * f)(N) ≤ Σ_{a ≤ N} f(a)²`, from `2xy ≤ x² + y²` and the reflection `a ↦ N - a`. -/
theorem conv_le_sum_sq (f : ℕ → ℤ) (N : ℕ) :
    conv f N ≤ ∑ a ∈ range (N + 1), f a ^ 2 := by
  have hrefl : ∑ a ∈ range (N + 1), f (N - a) ^ 2 = ∑ a ∈ range (N + 1), f a ^ 2 := by
    have := Finset.sum_range_reflect (fun a => f a ^ 2) (N + 1)
    simpa using this
  have h2 : 2 * conv f N ≤ ∑ a ∈ range (N + 1), f a ^ 2 + ∑ a ∈ range (N + 1), f (N - a) ^ 2 := by
    rw [conv, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    nlinarith [sq_nonneg (f a - f (N - a))]
  linarith

/-- NEW. Sign patterns symmetric about `N/2` attain the bound: `(ε * ε)(N) = N + 1`.
Plain math: if `ε(a)² = 1` and `ε(N - a) = ε(a)` for `a ≤ N`, every term is `1`. -/
theorem conv_symm_signs (ε : ℕ → ℤ) (N : ℕ) (hsq : ∀ a, ε a * ε a = 1)
    (hsym : ∀ a ≤ N, ε (N - a) = ε a) : conv ε N = N + 1 := by
  rw [conv]
  have : ∀ a ∈ range (N + 1), ε a * ε (N - a) = 1 := by
    intro a ha
    rw [hsym a (by simp at ha; omega)]; exact hsq a
  rw [Finset.sum_congr rfl this]; simp

/-- The period four sign pattern `+ - - +`. -/
def eps4 (a : ℕ) : ℤ := if a % 4 = 1 ∨ a % 4 = 2 then -1 else 1

/-- HELPER. Each block of four sums to zero, so `Σ_{a < 4k} eps4 a = 0`. -/
theorem sum_eps4 (k : ℕ) : ∑ a ∈ range (4 * k), eps4 a = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    simp only [eps4]
    have h0 : (4 * k) % 4 = 0 := by omega
    have h1 : (4 * k + 1) % 4 = 1 := by omega
    have h2 : (4 * k + 1 + 1) % 4 = 2 := by omega
    have h3 : (4 * k + 1 + 1 + 1) % 4 = 3 := by omega
    simp [h0, h1, h2, h3]

/-- NEW. Averaged statistic zero, pointwise value maximal.
Plain math: for every `N = 4k + 3` there is a `±1` sequence `ε` on `[0, N]` with
`Σ ε = 0`, so the full average `Σ_M (ε * ε)(M) = (Σ ε)² = 0` over the box, while
`(ε * ε)(N) = N + 1`, the `L²` maximum. Averaged, Fourier or Gowers data of low complexity
cannot bound the convolution at one fixed `N` away from its `L²` ceiling. -/
theorem averaged_zero_pointwise_max (k : ℕ) :
    ∃ ε : ℕ → ℤ, (∀ a, ε a * ε a = 1) ∧
      ∑ a ∈ range (4 * k + 3 + 1), ε a = 0 ∧ conv ε (4 * k + 3) = 4 * k + 3 + 1 := by
  refine ⟨eps4, ?_, ?_, ?_⟩
  · intro a; unfold eps4; split_ifs <;> norm_num
  · rw [show 4 * k + 3 + 1 = 4 * (k + 1) by ring]; exact sum_eps4 (k + 1)
  · have := conv_symm_signs eps4 (4 * k + 3) (by intro a; unfold eps4; split_ifs <;> norm_num)
      (by
        intro a ha
        unfold eps4
        have : (4 * k + 3 - a) % 4 = 3 - a % 4 := by omega
        rw [this]
        rcases (show a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 by omega) with h | h | h | h <;>
          simp [h])
    rw [this]; push_cast; ring

/-- NEW. The full average is the square of the sum, `Σ_{a,b < K} f(a) f(b) = (Σ f)²`:
the box average of the convolution only sees `Σ f`. -/
theorem box_average (f : ℕ → ℤ) (K : ℕ) :
    ∑ a ∈ range K, ∑ b ∈ range K, f a * f b = (∑ a ∈ range K, f a) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]

/-- Vacuity check: the hypotheses of `conv_symm_signs` are satisfiable, at `N = 3`. -/
example : (∀ a ≤ 3, eps4 (3 - a) = eps4 a) ∧ conv eps4 3 = 4 ∧
    ∑ a ∈ range 4, eps4 a = 0 := by decide

/-- Vacuity check at the primes: `(Λ_P * Λ_P)(10)` with `Λ_P` the prime indicator,
counted ordered: `10 = 3 + 7 = 5 + 5 = 7 + 3`, value `3`, below the `L²` ceiling `4`. -/
example : conv (fun a => if Nat.Prime a then 1 else 0) 10 = 3 := by decide

example : ∑ a ∈ range 11, (if Nat.Prime a then (1 : ℤ) else 0) ^ 2 = 4 := by decide

end LeanLab.Routes.R0045
