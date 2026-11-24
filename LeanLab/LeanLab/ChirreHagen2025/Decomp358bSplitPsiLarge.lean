import LeanLab.ChirreHagen2025.Decomp358b

/-!
Split of `Decomp358b.schoenfeld_psi_large`.
Schoenfeld 1976, Math. Comp. 30, pages 337 to 339, proof of Theorem 10, displays 6.6 to 6.12.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp358bSplitPsiLarge
open LeanLab.ChirreHagen2025.Decomp358b

/-- LEAF: Schoenfeld 1976 page 338 display 6.11 with page 339 line 1, the case xi = e^16:
under RH, with S3 = S4 = 0 and Lemmas 8 and 9 for m = 1, one has
|psi x - x| / x < log x * (log x - a5) / (8 pi sqrt x) for x at least e^16,
where a5 from display 6.12 is positive at xi = e^16. Class HARD. -/
theorem schoenfeld_6_11_at_e16 (hRH : RiemannHypothesis) :
    ∃ a5 : ℝ, 0 < a5 ∧ ∀ x : ℝ, Real.exp 16 ≤ x →
      |Chebyshev.psi x - x| / x <
        Real.log x * (Real.log x - a5) / (8 * Real.pi * Real.sqrt x) := by
  sorry

/-- Schoenfeld 1976 page 339 line 1: display 6.2 for x at least e^16 follows from 6.11.
CONDITIONAL ON the LEAF `schoenfeld_6_11_at_e16`. -/
theorem schoenfeld_psi_large_of_leaves (hRH : RiemannHypothesis) (y : ℝ)
    (hy : Real.exp 16 ≤ y) :
    |Chebyshev.psi y - y| ≤ Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi) := by
  obtain ⟨a5, ha5, h⟩ := schoenfeld_6_11_at_e16 hRH
  have hb := h y hy
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos 16) hy
  have hL : 0 < Real.log y := by
    have : (16 : ℝ) ≤ Real.log y := by
      rw [← Real.log_exp 16]; exact Real.log_le_log (Real.exp_pos 16) hy
    linarith
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < 8 * Real.pi * Real.sqrt y := by positivity
  have h2 : Real.log y * (Real.log y - a5) / (8 * Real.pi * Real.sqrt y) ≤
      Real.log y ^ 2 / (8 * Real.pi * Real.sqrt y) := by
    apply div_le_div_of_nonneg_right _ hden.le
    nlinarith
  have h3 : |Chebyshev.psi y - y| / y ≤ Real.log y ^ 2 / (8 * Real.pi * Real.sqrt y) :=
    hb.le.trans h2
  rw [div_le_iff₀ hy0] at h3
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  calc |Chebyshev.psi y - y| ≤ Real.log y ^ 2 / (8 * Real.pi * Real.sqrt y) * y := h3
    _ = Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi) := by
      have hs0 : Real.sqrt y ≠ 0 := hs.ne'
      field_simp
      simp [Real.sq_sqrt hy0.le]

end LeanLab.ChirreHagen2025.Decomp358bSplitPsiLarge
