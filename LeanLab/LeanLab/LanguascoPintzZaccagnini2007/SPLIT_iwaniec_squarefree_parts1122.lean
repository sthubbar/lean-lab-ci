import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_no_zero_open_strip481_steps

/-!
A split of the leaf `iwaniec_squarefree_series_bound1122` of
`SPLIT_iwaniec_squarefree_series1122`, the bound `Σ |μ(n)| n^(-σ) < 1 / (σ - 1)` of the line
before display (16) on page 103 of H. Iwaniec, On zeros of Dirichlet's L series,
Invent. Math. 23, 1974, 97 to 104, into the two analytic inputs of that line:
* no multiple of 4 is squarefree, so `Σ |μ(n)| n^(-σ) ≤ (1 - 4^(-σ)) ζ(σ)`;
* `ζ(σ) ≤ σ / (σ - 1)` for `σ > 1`.
The numerical step `σ (1 - 4^(-σ)) ≤ 1` on `1 < σ ≤ 6/5` is proved in the assembly, from
`4^6 ≤ 6^5`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF: Iwaniec 1974 page 103, the line before display (16), the squarefree saving.
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103: in
`Σ |μ(n)| n^(-σ)` every multiple of 4 has `μ(n) = 0`, so the sum is at most
`Σ_{4 ∤ n} n^(-σ) = (1 - 4^(-σ)) ζ(σ)`. In Lean the `n = 0` terms are `0` on both sides. -/
theorem iwaniec_squarefree_saving1122 (σ : ℝ) (hσ : 1 < σ) :
    ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
      (σ : ℂ) n‖ ≤ (1 - (4 : ℝ) ^ (-σ)) * ∑' n : ℕ, 1 / (n : ℝ) ^ σ := by
  sorry

/-- LEAF: Iwaniec 1974 page 103, the bound for `ζ(σ)` used in the line before display (16).
Class: MEDIUM.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103: for `σ > 1`,
`ζ(σ) = Σ n^(-σ) ≤ 1 + ∫₁^∞ x^(-σ) dx = σ / (σ - 1)`. In Lean the `n = 0` term is `0`. -/
theorem iwaniec_zeta_real_upper1122 (σ : ℝ) (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ σ ≤ σ / (σ - 1) := by
  sorry

end

end LeanLab.LPZ2007
