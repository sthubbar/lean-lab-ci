import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_no_zero_open_strip481_steps

/-!
A split of the leaf `iwaniec_inverse_series_bound1122` of `SPLIT_iwaniec_centre_lower1122`
along the line before display (16) on page 103 of H. Iwaniec, On zeros of Dirichlet's L series,
Invent. Math. 23, 1974, 97 to 104, read on the page image of `papers/Iwaniec1974.pdf`:
`|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / (σ₀ - 1)`.

The termwise step, `|χ(n) μ(n) n^(-s)| ≤ |μ(n)| n^(-σ)`, is proved in the assembly
`iwaniec_inverse_series_bound1122`. The remaining real inequality
`Σ |μ(n)| n^(-σ) ≤ 1 / (σ - 1)` on `1 < σ ≤ 6/5` is the leaf below.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF: Iwaniec 1974 page 103, the line before display (16), `Σ |μ(n)| n^(-σ) < 1 / (σ - 1)`.
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103. Here
`‖LSeries.term μ σ n‖ = |μ(n)| n^(-σ)` for `n ≥ 1` and `0` for `n = 0`, so the sum is
`ζ(σ) / ζ(2σ)`. One route: no multiple of 4 is squarefree, so the sum is at most
`ζ(σ) (1 - 4^(-σ))`; `ζ(σ) ≤ σ / (σ - 1)` by comparison with `∫₁^∞ x^(-σ) dx`; and
`σ (1 - 4^(-σ)) ≤ 1` for `1 < σ ≤ 6/5`. -/
theorem iwaniec_squarefree_series_bound1122 (σ : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
      (σ : ℂ) n‖ ≤ 1 / (σ - 1) := by
  sorry

end

end LeanLab.LPZ2007
