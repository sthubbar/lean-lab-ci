import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_no_zero_open_strip481_steps

/-!
A split of the leaf `iwaniec_centre_lower1122` of `SPLIT_iwaniec_display16_17_1122` along the
line before display (16) on page 103 of H. Iwaniec, On zeros of Dirichlet's L series,
Invent. Math. 23, 1974, 97 to 104, read on the page image of `papers/Iwaniec1974.pdf`:
`|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / (σ₀ - 1)`.

The first step, that `L(s, χ)` and the series `Σ χ(n) μ(n) n^(-s)` are inverse for `re s > 1`,
is Mathlib's `LSeries.mul_mu_eq_one` and is used directly in the assembly
`iwaniec_centre_lower1122` of `SPLIT_iwaniec_display16_17_1122`. The second step, the bound of
the inverse series by `Σ |μ(n)| n^(-σ) < 1 / (σ - 1)`, is the leaf below.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF: Iwaniec 1974 page 103, the line before display (16), the bound
`|Σ χ(n) μ(n) n^(-s)| ≤ Σ |μ(n)| n^(-σ) < 1 / (σ - 1)`.
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103: the inverse
series of `L(s, χ)` is bounded termwise by `Σ |μ(n)| n^(-σ) = ζ(σ) / ζ(2σ)`, and on
`1 < σ ≤ 6/5` this is below `1 / (σ - 1)`. One route: `Σ |μ(n)| n^(-σ) ≤ ζ(σ) (1 - 4^(-σ))`,
`ζ(σ) ≤ σ / (σ - 1)`, and `σ (1 - 4^(-σ)) ≤ 1` for `1 < σ ≤ 6/5`. -/
theorem iwaniec_inverse_series_bound1122 (q : ℕ) (ψ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    ‖LSeries (fun n : ℕ => ψ n * ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 / (σ - 1) := by
  sorry

end

end LeanLab.LPZ2007
