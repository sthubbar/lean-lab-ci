/-
P0069 Baker, Harman, Pintz 1997, Theorem 4, page 12, with the definitions of Section 3,
page 11, read from the page images papers/P0069-original.pdf. Unit U-5050,
CLOUD 20261019T0213Z-cloud14.

STATED as a cited Prop: `Theorem4`, the mean value bound ‖MNL‖₁ ≪ X^{1/2} ℒ^{-A} for three
Dirichlet polynomials of lengths M = X^{α₁}, N = X^{α₂}, L = X/(MN) over a well-spaced set of
pairs (t, χ). The exponent steps of its proof are PROVED in Thm4Exponents.lean.
PROVED: `admissible_point`, a vacuity test, the hypotheses (3.6), (3.7) and the range of θ hold
together at θ = 0.55, ε = 0.001, α₁ = 0.41, α₂ = 0.45.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib
import LeanLab.BHP1997.Thm4Exponents

namespace LeanLab.BHP1997.Thm4

open Complex

/-- A Dirichlet polynomial `F(s, χ) = Σ_{n ≍ F} a_n χ(n) n^{-s}`, with `n ≍ F` read as
`c₁ F < n < c₂ F`, page 11. -/
noncomputable def dirPoly {q : ℕ} (a : ℕ → ℂ) (c₁ c₂ F : ℝ) (χ : DirichletCharacter ℂ q)
    (s : ℂ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F),
    a n * χ (n : ZMod q) / (n : ℂ) ^ s

/-- The point `1/2 + it`. -/
noncomputable def half (t : ℝ) : ℂ := 1 / 2 + t * I

/-- `S` is well-spaced: `|t - t'| ≥ 1` for distinct pairs with the same character, page 11. -/
def WellSpaced {q : ℕ} (S : Finset (ℝ × DirichletCharacter ℂ q)) : Prop :=
  ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.2 = p'.2 → 1 ≤ |p.1 - p'.1|

/-- (3.1): `|a_n| ≤ τ(n)^B`. -/
def CoeffBound (a : ℕ → ℂ) (B : ℝ) : Prop :=
  ∀ n : ℕ, ‖a n‖ ≤ ((n.divisors.card : ℕ) : ℝ) ^ B

/-- Theorem 4, page 12, CITED. ℒ = log x; `X` is one of `x`, `Y² = x^{2θ₁}` with
`θ₁ = 11/20 + ε`. For `1/2 + ε < θ < 7/12`, `qT = X^{1-θ}`, `M = X^{α₁}`, `N = X^{α₂}`,
`MNL = X` with (3.6) and (3.7), coefficients bounded by (3.1), and `L` satisfying (3.2) with
implied constants `K A'`, the sum over the well-spaced set `S ⊆ [-T, T] × {χ mod q}` of
`|M N L (1/2 + it, χ)|` is at most `C X^{1/2} ℒ^{-A}`. The Remark on page 3 says implied
constants depend at most on `A`; the lab lets `C` depend on `A`, `ε`, `B`, `c₁`, `c₂` and the
constants `K` of (3.2), uniformly in everything else. -/
def Theorem4 (ε B : ℝ) : Prop :=
  ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ S, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)

/-- Vacuity test: the exponent hypotheses of Theorem 4 hold together at θ = 0.55, ε = 0.001,
α₁ = 0.41, α₂ = 0.45, so `L = X^{0.14}`. -/
theorem admissible_point :
    1 / 2 + (0.001 : ℝ) < 0.55 ∧ (0.55 : ℝ) < 7 / 12 ∧
      |(0.41 : ℝ) - 0.45| < 2 * 0.55 - 1 - 0.001 ∧ 1 - ((0.41 : ℝ) + 0.45) < gam 0.55 - 0.001 := by
  obtain ⟨-, -, h3, h4, -⟩ := printed_sign_false
  exact ⟨by norm_num, by norm_num, h3, h4⟩

/-- Theorem 4 as the paper asserts it: `ε` small and positive, `Bε` small, page 3. -/
def Theorem4Paper : Prop :=
  ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → Theorem4 ε B

end LeanLab.BHP1997.Thm4
