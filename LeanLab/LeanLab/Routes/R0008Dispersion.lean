import Mathlib

/-!
# R-0008, the Friedlander-Iwaniec asymptotic sieve route for A = {N - p}

T3 MOONSHOT, unit U-1042, run 20261019T0803Z-3015. AI wrote this Lean code.

The asymptotic sieve of Friedlander and Iwaniec breaks parity with a Type II, bilinear,
estimate for the sequence. For A = {N - p} the Type II sum is
`Σ_{m ∈ I} |Σ_{n ∈ J} β n · a(m n)|` with `a k = 1` when `N - k` is prime.
Linnik's dispersion step, Cauchy-Schwarz in `m`, bounds its square by the card of `I` times
`Σ_{n₁, n₂} β n₁ β n₂ · #{m ∈ I : N - m n₁ and N - m n₂ both prime}`,
a two-prime correlation along a linear family, as hard as a twin prime or Goldbach count.
This file proves that step and the identification of the inner sum. KNOWN mathematics.
-/

namespace LeanLab.Routes.R0008

open Finset

/-- The row of a Type II sum: `x_m = Σ_{n ∈ J} β n · a (m n)`. -/
def row (a β : ℕ → ℝ) (J : Finset ℕ) (m : ℕ) : ℝ := ∑ n ∈ J, β n * a (m * n)

/-- Linnik's dispersion step: Cauchy-Schwarz in `m`, then expand the square. -/
theorem dispersion (a β : ℕ → ℝ) (I J : Finset ℕ) :
    (∑ m ∈ I, |row a β J m|) ^ 2 ≤
      (I.card : ℝ) * ∑ n₁ ∈ J, ∑ n₂ ∈ J,
        β n₁ * β n₂ * ∑ m ∈ I, a (m * n₁) * a (m * n₂) := by
  have h1 : (∑ m ∈ I, |row a β J m|) ^ 2 ≤ (I.card : ℝ) * ∑ m ∈ I, |row a β J m| ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : ∑ m ∈ I, |row a β J m| ^ 2 = ∑ n₁ ∈ J, ∑ n₂ ∈ J,
      β n₁ * β n₂ * ∑ m ∈ I, a (m * n₁) * a (m * n₂) := by
    have hm : ∀ m, |row a β J m| ^ 2 = ∑ n₁ ∈ J, ∑ n₂ ∈ J,
        β n₁ * β n₂ * (a (m * n₁) * a (m * n₂)) := by
      intro m
      rw [sq_abs, sq, row, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    rw [Finset.sum_congr rfl (fun m _ => hm m), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n₁ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n₂ _ => ?_)
    rw [Finset.mul_sum]
  rw [h2] at h1
  exact h1

/-- The indicator of `A = {N - p}`: `aN N k = 1` when `k < N` and `N - k` is prime. -/
def aN (N k : ℕ) : ℝ := if k < N ∧ (N - k).Prime then 1 else 0

/-- The inner sum of the dispersion is a two-prime count along a linear family in `m`. -/
theorem corr_eq (N n₁ n₂ : ℕ) (I : Finset ℕ) :
    ∑ m ∈ I, aN N (m * n₁) * aN N (m * n₂) =
      ((I.filter fun m => (m * n₁ < N ∧ (N - m * n₁).Prime) ∧
          (m * n₂ < N ∧ (N - m * n₂).Prime)).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun m _ => ?_)
  unfold aN
  split_ifs <;> simp_all

/-- The dispersion bound for the Goldbach sequence: the Type II sum of `A = {N - p}` is
controlled by two-prime correlations `#{m ∈ I : N - m n₁, N - m n₂ both prime}`. -/
theorem dispersion_goldbach (N : ℕ) (β : ℕ → ℝ) (I J : Finset ℕ) :
    (∑ m ∈ I, |row (aN N) β J m|) ^ 2 ≤
      (I.card : ℝ) * ∑ n₁ ∈ J, ∑ n₂ ∈ J, β n₁ * β n₂ *
        ((I.filter fun m => (m * n₁ < N ∧ (N - m * n₁).Prime) ∧
          (m * n₂ < N ∧ (N - m * n₂).Prime)).card : ℝ) := by
  have h := dispersion (aN N) β I J
  simp only [corr_eq] at h
  exact h

/-- Vacuity test: the indicator is not identically zero, `10 - 3 = 7` is prime. -/
example : aN 10 3 = 1 := by
  norm_num [aN]

/-- Vacuity test: a nonzero two-prime count, `m = 1`, `n₁ = 3`, `n₂ = 5`, `N = 10`:
`10 - 3 = 7` and `10 - 5 = 5` are prime. -/
example : ∑ m ∈ ({1} : Finset ℕ), aN 10 (m * 3) * aN 10 (m * 5) = 1 := by
  norm_num [aN]

end LeanLab.Routes.R0008
