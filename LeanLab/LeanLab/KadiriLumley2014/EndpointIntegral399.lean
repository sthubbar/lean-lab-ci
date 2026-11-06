/-
P0059 page 5 Section 2.5 and source 4, arXiv 1310.6374 page 8 Corollary 2.6.
Strict and inclusive zero counts differ only on a countable set of ordinates.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.CountEndpoint399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory Filter Topology
open Task259

/-- Strict and inclusive counts agree almost everywhere for real Lebesgue measure. -/
theorem inclusiveCount_ae_eq_zeroCount : inclusiveCount =ᵐ[volume] zeroCount := by
  have hz : riemannZetaZeros.Countable :=
    isClosed_riemannZetaZeros.isLindelof.countable_of_isDiscrete isDiscrete_riemannZetaZeros
  have hae := (hz.image Complex.im).ae_notMem (volume : Measure ℝ)
  filter_upwards [hae] with t ht
  unfold inclusiveCount zeroCount positiveZeroSum
  apply tsum_congr
  intro ρ
  have hne : (ρ : ℂ).im ≠ t := by
    intro he
    exact ht ⟨ρ, mem_riemannZetaZeros.mpr ρ.property.1, he⟩
  have hiff : (ρ : ℂ).im ≤ t ↔ (ρ : ℂ).im < t := by
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact hlt
      · exact False.elim (hne heq)
    · exact le_of_lt
  simp only [hiff]

/-- Replacing the strict count by its inclusive version does not change any weighted interval integral.
No integrability hypothesis is needed for this equality of Bochner integrals. -/
theorem integral_inclusiveCount (f : ℝ → ℝ) (U V : ℝ) :
    (∫ t in U..V, inclusiveCount t * f t) = ∫ t in U..V, zeroCount t * f t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [inclusiveCount_ae_eq_zeroCount] with t ht
  intro _
  rw [ht]

end LeanLab.KadiriLumley2014.Task399
