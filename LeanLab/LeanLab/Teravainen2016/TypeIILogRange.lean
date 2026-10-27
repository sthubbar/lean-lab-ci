/-
P0076 Section 11, pages 46 to 47. The logarithmic factor in the frequency range R.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.TypeIISaving

open Filter
open scoped Topology

namespace LeanLab.Teravainen2016

/-- The frequency range R may include any fixed natural power of log N, as on page 46. -/
theorem typeII_log_range_saving (C : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N₀ : ℝ, ∀ N R M D₁ D₂ θ : ℝ, N₀ ≤ N → 0 < M → 0 ≤ R →
      R ≤ N ^ θ * (Real.log N) ^ C → TypeIIConditions N M D₁ D₂ θ ε →
      (Real.log N) ^ 1000 * typeIIKernel N R M D₁ D₂ ≤ 4 * N ^ (1 - ε ^ 2 / 10) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_log_pow_le_rpow (1000 + C)
    (show 0 < 2 * ε ^ 2 / 5 by positivity))
  refine ⟨max 2 A, ?_⟩
  intro N R M D₁ D₂ θ hN hM hR0 hR hcond
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hL : 0 < (Real.log N) ^ C := pow_pos hlogpos C
  have hsmallR : R / (Real.log N) ^ C ≤ N ^ θ := (div_le_iff₀ hL).mpr hR
  have hsmallR0 : 0 ≤ R / (Real.log N) ^ C := div_nonneg hR0 hL.le
  have hker := typeII_kernel_saving hN1 hM hsmallR0 hsmallR hε hε1 hcond
  have hD : 0 < D₁ := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hcond.2.2.1
  have hker0 : 0 ≤ typeIIKernel N (R / (Real.log N) ^ C) M D₁ D₂ := by
    unfold typeIIKernel
    positivity
  have hscale : typeIIKernel N R M D₁ D₂ =
      (Real.log N) ^ C * typeIIKernel N (R / (Real.log N) ^ C) M D₁ D₂ := by
    unfold typeIIKernel
    field_simp [hL.ne']
  have hlog := hA N ((le_max_right _ _).trans hN)
  calc
    _ = (Real.log N) ^ (1000 + C) * typeIIKernel N (R / (Real.log N) ^ C) M D₁ D₂ := by
      rw [hscale, pow_add]
      ring
    _ ≤ N ^ (2 * ε ^ 2 / 5) * (4 * N ^ (1 - ε ^ 2 / 2)) :=
      mul_le_mul hlog hker hker0 (by positivity)
    _ = 4 * N ^ (1 - ε ^ 2 / 10) := by
      rw [show N ^ (2 * ε ^ 2 / 5) * (4 * N ^ (1 - ε ^ 2 / 2)) =
        4 * (N ^ (2 * ε ^ 2 / 5) * N ^ (1 - ε ^ 2 / 2)) by ring, ← Real.rpow_add hN0]
      congr 2
      ring

#print axioms typeII_log_range_saving

end LeanLab.Teravainen2016
