/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp362a

namespace LeanLab.Tchudakov1938.Decomp362k
open Real

/-- P0064, page 36, inequality 30. Continuity and positivity of sinc on a compact subinterval give the stated positive linear sine bound. -/
theorem sine_lower : ∃ c : ℝ, 0 < c ∧ ∀ φ : ℝ, |φ| ≤ (5 / 6 : ℝ) * Real.pi → c * |φ| ≤ |Real.sin φ| := by
  let a : ℝ := (5 / 6 : ℝ) * Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have hapi : a < Real.pi := by dsimp [a]; nlinarith [Real.pi_pos]
  have hpos : ∀ φ ∈ Set.Icc (-a) a, 0 < Real.sinc φ := by
    intro φ hφ
    have habs : |φ| ≤ a := abs_le.mpr hφ
    exact Real.sinc_pos (habs.trans_lt hapi)
  obtain ⟨φ₀, hφ₀, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Set.Icc (-a) a)
    ⟨0, by constructor <;> linarith⟩ Real.continuous_sinc.continuousOn
  refine ⟨Real.sinc φ₀, hpos φ₀ hφ₀, fun φ hφ => ?_⟩
  have hle : Real.sinc φ₀ ≤ Real.sinc φ := hmin (abs_le.mp hφ)
  have hsinc : 0 ≤ Real.sinc φ := (hpos φ (abs_le.mp hφ)).le
  have hmul := mul_le_mul_of_nonneg_right hle (abs_nonneg φ)
  have heq : Real.sinc φ * |φ| = |Real.sin φ| := by
    by_cases hz : φ = 0
    · simp [hz]
    · rw [Real.sinc_of_ne_zero hz]
      have hh : Real.sin φ / φ * φ = Real.sin φ := div_mul_cancel₀ _ hz
      have hh' := congrArg abs hh
      rw [Real.sinc_of_ne_zero hz] at hsinc
      rw [abs_mul, abs_of_nonneg hsinc] at hh'
      exact hh'
  rwa [heq] at hmul

end LeanLab.Tchudakov1938.Decomp362k
