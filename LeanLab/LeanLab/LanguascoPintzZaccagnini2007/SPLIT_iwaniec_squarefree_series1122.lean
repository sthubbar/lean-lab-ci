import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_iwaniec_squarefree_parts1122

/-!
A split of the leaf `iwaniec_inverse_series_bound1122` of `SPLIT_iwaniec_centre_lower1122`
along the line before display (16) on page 103 of H. Iwaniec, On zeros of Dirichlet's L series,
Invent. Math. 23, 1974, 97 to 104, read on the page image of `papers/Iwaniec1974.pdf`:
`|L(s₀, χ)|⁻¹ ≤ Σ |μ(n)| n^(-σ₀) < 1 / (σ₀ - 1)`.

The termwise step, `|χ(n) μ(n) n^(-s)| ≤ |μ(n)| n^(-σ)`, is proved in the assembly
`iwaniec_inverse_series_bound1122`. The remaining real inequality
`Σ |μ(n)| n^(-σ) ≤ 1 / (σ - 1)` on `1 < σ ≤ 6/5` is proved below from the two leaves of
`SPLIT_iwaniec_squarefree_parts1122`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- Iwaniec 1974 page 103, the line before display (16), `Σ |μ(n)| n^(-σ) < 1 / (σ - 1)`.
Formerly a MEDIUM leaf, now proved from the leaves `iwaniec_squarefree_saving1122` and
`iwaniec_zeta_real_upper1122` of `SPLIT_iwaniec_squarefree_parts1122` and the numerical step
`σ (1 - 4^(-σ)) ≤ 1`, from `4^6 ≤ 6^5`.
H. Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23, 1974, page 103. Here
`‖LSeries.term μ σ n‖ = |μ(n)| n^(-σ)` for `n ≥ 1` and `0` for `n = 0`, so the sum is
`ζ(σ) / ζ(2σ)`. One route: no multiple of 4 is squarefree, so the sum is at most
`ζ(σ) (1 - 4^(-σ))`; `ζ(σ) ≤ σ / (σ - 1)` by comparison with `∫₁^∞ x^(-σ) dx`; and
`σ (1 - 4^(-σ)) ≤ 1` for `1 < σ ≤ 6/5`. -/
theorem iwaniec_squarefree_series_bound1122 (σ : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
      (σ : ℂ) n‖ ≤ 1 / (σ - 1) := by
  have hA := iwaniec_squarefree_saving1122 σ hσ
  have hB := iwaniec_zeta_real_upper1122 σ hσ
  set S := ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
      (σ : ℂ) n‖ with hS
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ σ with hZ
  have h4 : (4 : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hmono : (4 : ℝ) ^ (-(6 / 5 : ℝ)) ≤ (4 : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hval : (1 / 6 : ℝ) ≤ (4 : ℝ) ^ (-(6 / 5 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), one_div_le (by norm_num) (by positivity)]
    have h5 : ((4 : ℝ) ^ (6 / 5 : ℝ)) ^ (5 : ℕ) = 4096 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hp : 0 ≤ (4 : ℝ) ^ (6 / 5 : ℝ) := by positivity
    rw [one_div, inv_inv]
    by_contra hc
    rw [not_le] at hc
    have : (6 : ℝ) ^ 5 < ((4 : ℝ) ^ (6 / 5 : ℝ)) ^ 5 := by gcongr
    rw [h5] at this; norm_num at this
  have hσ1 : 0 < σ - 1 := by linarith
  have hkey : σ * (1 - (4 : ℝ) ^ (-σ)) ≤ 1 := by nlinarith
  calc S ≤ (1 - (4 : ℝ) ^ (-σ)) * Z := hA
    _ ≤ (1 - (4 : ℝ) ^ (-σ)) * (σ / (σ - 1)) := mul_le_mul_of_nonneg_left hB (by linarith)
    _ = σ * (1 - (4 : ℝ) ^ (-σ)) / (σ - 1) := by ring
    _ ≤ 1 / (σ - 1) := by gcongr

end

end LeanLab.LPZ2007
