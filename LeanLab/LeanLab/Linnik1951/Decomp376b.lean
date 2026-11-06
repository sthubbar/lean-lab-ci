/-
P0093 pages 158 and 159. The central Mellin interval from its pointwise bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357a

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 158 pointwise estimate immediately before equation
4.8, transferred to the nonprincipal character sum by page 159 equation
5.1. This is the squared bound on the central interval only. It has no
integration or outer interval conclusion. -/
theorem central_pointwise376 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ,
          |α| ≤ 4 / (N : ℝ) →
            ‖characterPrime280 χ N α‖ ^ 2 ≤
              B * (N : ℝ) ^ 2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  sorry

/-- P0093 page 158 equation 4.8. Exact mellin_near357 statement from the
central pointwise estimate. The interval has length eight over N.
CONDITIONAL only on central_pointwise376. -/
theorem mellin_near_decomposed376 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(4 / (N : ℝ))..(4 / (N : ℝ)),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  obtain ⟨B, hB, N0, hb⟩ := central_pointwise376 hG
  refine ⟨8 * B, by positivity, max 1 N0, ?_⟩
  intro N hN q hq hqt χ hχ
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hab : -(4 / (N : ℝ)) ≤ 4 / (N : ℝ) := by
    have : 0 ≤ 4 / (N : ℝ) := by positivity
    linarith
  calc
    _ ≤ ∫ _α in -(4 / (N : ℝ))..(4 / (N : ℝ)),
        B * (N : ℝ) ^ 2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
      apply intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
        intervalIntegrable_const
      intro α hα
      exact hb N hN0 q hq hqt χ hχ α (abs_le.mpr hα)
    _ = _ := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hd : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≠ 0 := by positivity
      field_simp [hNp.ne', hd]
      <;> ring

end LeanLab.Linnik1951
