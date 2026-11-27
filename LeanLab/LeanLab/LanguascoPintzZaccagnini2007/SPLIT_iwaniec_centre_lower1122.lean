import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_squarefree_series1122

/-!
A split of the leaf `iwaniec_centre_lower1122` of `SPLIT_iwaniec_display16_17_1122` along the
line before display (16) on page 103 of H. Iwaniec, On zeros of Dirichlet's L series,
Invent. Math. 23, 1974, 97 to 104, read on the page image of `papers/Iwaniec1974.pdf`:
`|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / (σ₀ - 1)`.

The first step, that `L(s, χ)` and the series `Σ χ(n) μ(n) n^(-s)` are inverse for `re s > 1`,
is Mathlib's `LSeries.mul_mu_eq_one` and is used directly in the assembly
`iwaniec_centre_lower1122` of `SPLIT_iwaniec_display16_17_1122`. The second step, the bound of
the inverse series by `Σ |μ(n)| n^(-σ) < 1 / (σ - 1)`, is proved below termwise from the
leaf of `SPLIT_iwaniec_squarefree_series1122`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- Iwaniec 1974 page 103, the line before display (16), the bound
`|Σ χ(n) μ(n) n^(-s)| ≤ Σ |μ(n)| n^(-σ) < 1 / (σ - 1)`.
Formerly a MEDIUM leaf, now proved termwise from the leaf `iwaniec_squarefree_series_bound1122`
of `SPLIT_iwaniec_squarefree_series1122`.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103: the inverse
series of `L(s, χ)` is bounded termwise by `Σ |μ(n)| n^(-σ) = ζ(σ) / ζ(2σ)`, and on
`1 < σ ≤ 6/5` this is below `1 / (σ - 1)`. One route: `Σ |μ(n)| n^(-σ) ≤ ζ(σ) (1 - 4^(-σ))`,
`ζ(σ) ≤ σ / (σ - 1)`, and `σ (1 - 4^(-σ)) ≤ 1` for `1 < σ ≤ 6/5`. -/
theorem iwaniec_inverse_series_bound1122 (q : ℕ) (ψ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    ‖LSeries (fun n : ℕ => ψ n * ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 / (σ - 1) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  set g : ℕ → ℂ := fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ) with hg
  have hleaf := iwaniec_squarefree_series_bound1122 σ hσ hσ'
  have hgs : LSeriesSummable g (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by simpa using hσ)
  have hcmp : ∀ n, ‖LSeries.term (fun n : ℕ => ψ n * g n) s n‖ ≤
      ‖LSeries.term g (σ : ℂ) n‖ := by
    intro n
    have h1 : ‖LSeries.term (fun n : ℕ => ψ n * g n) s n‖ ≤ ‖LSeries.term g s n‖ := by
      apply LSeries.norm_term_le
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (ψ.norm_le_one n)
    have h2 : ‖LSeries.term g s n‖ = ‖LSeries.term g (σ : ℂ) n‖ := by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]; simp [hs]
    rw [← h2]; exact h1
  have hsum : Summable (fun n => ‖LSeries.term g (σ : ℂ) n‖) := hgs.norm
  have hsum' : Summable (fun n => ‖LSeries.term (fun n : ℕ => ψ n * g n) s n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcmp hsum
  calc ‖LSeries (fun n : ℕ => ψ n * g n) s‖
      ≤ ∑' n, ‖LSeries.term (fun n : ℕ => ψ n * g n) s n‖ := norm_tsum_le_tsum_norm hsum'
    _ ≤ ∑' n, ‖LSeries.term g (σ : ℂ) n‖ := Summable.tsum_le_tsum hcmp hsum' hsum
    _ ≤ 1 / (σ - 1) := hleaf

end

end LeanLab.LPZ2007
