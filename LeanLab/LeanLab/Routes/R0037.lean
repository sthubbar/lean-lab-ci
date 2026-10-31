import Mathlib

/-
# R-0037, T3 MOONSHOT: a Vaughan identity on one variable of the binary Goldbach count

Unit U-1345, PC run 20261021T0203Z-29730. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it. KNOWN mathematics,
Vaughan 1977.

The route: expand Λ(a) in r_Λ(N) = Σ_{a+b=N} Λ(a) Λ(b) by Vaughan's identity
  Λ = Λ₁ + μ₁ * log - μ₁ * Λ₁ * ζ + (μ - μ₁) * ζ * (Λ - Λ₁)
for ANY truncations μ₁, Λ₁, usually μ, Λ cut at U, V. The first three pieces are Type I sums
against the weight Λ(N - a); the last is the Type II bilinear piece Σ_{m > U, n > V} a_m b_n Λ(N - mn).

* `vaughan_ring`: the identity in any commutative ring from μζ = 1 and Λζ = L, pure algebra.
* `vaughan`: the identity in `ArithmeticFunction ℝ` for every μ₁, Λ₁.
* `goldbach_vaughan_split`: the binary count splits exactly into Type I and Type II parts.
-/

namespace LeanLab.Routes.R0037

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Vaughan's identity as ring algebra: only `μ ζ = 1` and `Λ ζ = L` are used. -/
theorem vaughan_ring {R : Type*} [CommRing R] (m z l L m₁ l₁ : R)
    (hm : m * z = 1) (hl : l * z = L) :
    l = l₁ + m₁ * L - m₁ * l₁ * z + (m - m₁) * z * (l - l₁) := by
  linear_combination (-(l - l₁)) * hm + m₁ * hl

/-- Vaughan's identity for the von Mangoldt function, any truncations `μ₁`, `Λ₁`. -/
theorem vaughan (μ₁ Λ₁ : ArithmeticFunction ℝ) :
    (Λ : ArithmeticFunction ℝ) = Λ₁ + μ₁ * log - μ₁ * Λ₁ * (ζ : ArithmeticFunction ℝ)
      + ((μ : ArithmeticFunction ℝ) - μ₁) * (ζ : ArithmeticFunction ℝ) * (Λ - Λ₁) :=
  vaughan_ring _ _ _ _ _ _ coe_moebius_mul_coe_zeta vonMangoldt_mul_zeta

/-- The binary Goldbach count r_Λ(N) is the Type I part plus the Type II part, exactly. -/
theorem goldbach_vaughan_split (μ₁ Λ₁ : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ x ∈ antidiagonal N, Λ x.1 * Λ x.2
      = ∑ x ∈ antidiagonal N,
          (Λ₁ + μ₁ * log - μ₁ * Λ₁ * (ζ : ArithmeticFunction ℝ)) x.1 * Λ x.2
        + ∑ x ∈ antidiagonal N,
          (((μ : ArithmeticFunction ℝ) - μ₁) * (ζ : ArithmeticFunction ℝ) * (Λ - Λ₁)) x.1
            * Λ x.2 := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← add_mul]
  congr 1
  conv_lhs => rw [vaughan μ₁ Λ₁]
  simp only [ArithmeticFunction.add_apply]

/-- With no truncation, μ₁ = Λ₁ = 0, the Type II piece is all of Λ: a split with no Type I part
is the original problem. -/
theorem vaughan_trivial_cut (n : ℕ) :
    (((μ : ArithmeticFunction ℝ) - 0) * (ζ : ArithmeticFunction ℝ) * (Λ - 0)) n = Λ n := by
  simp [coe_moebius_mul_coe_zeta]

end LeanLab.Routes.R0037
