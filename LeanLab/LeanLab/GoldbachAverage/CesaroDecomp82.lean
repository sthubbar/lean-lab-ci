import LeanLab.GoldbachAverage.UnconditionalCore

/-!
Decomposition of the corrected Cesaro formula cited in UnconditionalCore.lean.
Source: arXiv 1806.04930v2 pages 2 to 6, with both prime powers equal to one.
AI wrote this Lean code. Goldbach is open.
-/

open Complex Finset
open scoped ArithmeticFunction.vonMangoldt
noncomputable section
namespace LeanLab.GoldbachAverage.CesaroDecomp82

/-- The normalized weighted sum in the corrected formula, page 2. -/
def weighted (k : ℝ) (N : ℕ) : ℂ :=
  ((∑ n ∈ range (N + 1), G n * (1 - (n : ℝ) / N) ^ k / Real.Gamma (k + 1) : ℝ) : ℂ)

/-- The displayed main terms after Theorem 1, page 2. -/
def mainTerms (k : ℝ) (N : ℕ) : ℂ :=
  (N : ℂ) ^ 2 / (Real.Gamma (k + 3) : ℂ)
  - 2 * zeroSum (fun ρ => Gamma ρ / Gamma (ρ + k + 2) * (N : ℂ) ^ (ρ + 1))
  - 2 * (Real.log (2 * Real.pi) : ℂ) * (N : ℂ) / (Real.Gamma (k + 2) : ℂ)
  + 2 * (Real.log (2 * Real.pi) : ℂ) *
      zeroSum (fun ρ => Gamma ρ / Gamma (k + 1 + ρ) * (N : ℂ) ^ ρ)
  + zeroSum (fun ρ₁ => zeroSum (fun ρ₂ =>
      Gamma ρ₁ * Gamma ρ₂ / Gamma (ρ₁ + ρ₂ + k + 1) * (N : ℂ) ^ (ρ₁ + ρ₂)))

/-- The complex Laplace series, page 3 eq. 7, with prime power one. -/
def laplaceSeries (z : ℂ) : ℂ := ∑' n : ℕ, (Λ n : ℂ) * Complex.exp (-(n : ℂ) * z)

/-- The zero expansion M in Section 3, page 4, with prime power one. -/
def laplaceMain (z : ℂ) : ℂ :=
  1 / z - (Real.log (2 * Real.pi) : ℂ) - zeroSum (fun ρ => Gamma ρ * z ^ (-ρ))

/-- The normalized vertical line integral from Section 2, pages 3 and 4.
The contour has real part one over N. -/
def verticalAverage (f : ℂ → ℂ) (k : ℝ) (N : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * (N : ℂ) ^ (-(k : ℂ)) *
    ∫ y : ℝ, let z : ℂ := (1 / (N : ℝ) : ℝ) + Complex.I * y
      Complex.exp ((N : ℂ) * z) * z ^ (-(k : ℂ) - 1) * f z

/-- LEAF. Corrected source page 4, the fundamental relation of Section 2.
Laplace inversion and interchange with the absolutely convergent prime series.
The inversion formula is cited on page 2 eq. 5 from de Azevedo Pribitkin. -/
theorem weighted_eq_vertical (k : ℝ) (hk : 1 < k) (N : ℕ) (hN : 2 ≤ N) :
    weighted k N = verticalAverage (fun z => laplaceSeries z ^ 2) k N := by
  sorry

/-- LEAF. Corrected source pages 4 and 5, Section 3 eq. 12 and its three error integrals.
The complex zero expansion can replace the Laplace series with normalized error O of sqrt N. -/
theorem replacement_error (k : ℝ) (hk : 1 < k) : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖verticalAverage (fun z => laplaceSeries z ^ 2) k N -
      verticalAverage (fun z => laplaceMain z ^ 2) k N‖ ≤ K * (N : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/-- LEAF. Corrected source pages 5 and 6, evaluation of I1 through I5.
The single and double zero sums require the interchange proofs in Sections 5 and 6.
The constant M2 is retained here and absorbed only in the final error. -/
theorem main_vertical_evaluation (k : ℝ) (hk : 1 < k) (N : ℕ) (hN : 2 ≤ N) :
    verticalAverage (fun z => laplaceMain z ^ 2) k N =
      mainTerms k N + (Real.log (2 * Real.pi) ^ 2 / Real.Gamma (k + 1) : ℝ) := by
  sorry

/-- Corrected formula, page 2, assembled without sorry in the assembly.
CONDITIONAL ON the three analytic leaves. -/
theorem lz_cesaro_assembled (k : ℝ) (hk : 1 < k) : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ‖((∑ n ∈ range (N + 1), G n * (1 - (n : ℝ) / N) ^ k / Real.Gamma (k + 1) : ℝ) : ℂ)
      - (N : ℂ) ^ 2 / (Real.Gamma (k + 3) : ℂ)
      + 2 * zeroSum (fun ρ => Gamma ρ / Gamma (ρ + k + 2) * (N : ℂ) ^ (ρ + 1))
      + 2 * (Real.log (2 * Real.pi) : ℂ) * (N : ℂ) / (Real.Gamma (k + 2) : ℂ)
      - 2 * (Real.log (2 * Real.pi) : ℂ) * zeroSum (fun ρ => Gamma ρ / Gamma (k + 1 + ρ) * (N : ℂ) ^ ρ)
      - zeroSum (fun ρ₁ => zeroSum (fun ρ₂ =>
          Gamma ρ₁ * Gamma ρ₂ / Gamma (ρ₁ + ρ₂ + k + 1) * (N : ℂ) ^ (ρ₁ + ρ₂)))‖
      ≤ K * (N : ℝ) ^ ((1 : ℝ) / 2) := by
  obtain ⟨K, hK⟩ := replacement_error k hk
  set c : ℂ := ((Real.log (2 * Real.pi) ^ 2 / Real.Gamma (k + 1) : ℝ) : ℂ)
  refine ⟨K + ‖c‖, fun N hN => ?_⟩
  have he := hK N hN
  rw [← weighted_eq_vertical k hk N hN, main_vertical_evaluation k hk N hN] at he
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num)
  have hc := mul_le_mul_of_nonneg_left hpow (norm_nonneg c)
  have htri := norm_add_le (weighted k N - (mainTerms k N + c)) c
  have hid : weighted k N - (mainTerms k N + c) + c = weighted k N - mainTerms k N := by ring
  rw [hid] at htri
  have hbound : ‖weighted k N - mainTerms k N‖ ≤ (K + ‖c‖) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
    dsimp [c] at *
    nlinarith
  convert hbound using 1
  congr 1
  dsimp [weighted, mainTerms]
  ring

example : type_of% lz_cesaro := lz_cesaro_assembled

end LeanLab.GoldbachAverage.CesaroDecomp82
