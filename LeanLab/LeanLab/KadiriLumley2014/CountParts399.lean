/-
P0059 page 5 Section 2.5 and page 7 Lemma 2.5.
Source 4, arXiv 1310.6374 pages 8 and 9, Corollary 2.6.
Finite zero-count partial summation with explicit endpoint conventions.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.DensityBound399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory
open Task259

/-- All open-strip zeros have positive real part, so the density count at zero equals N. -/
theorem zeroCount_eq_densityCount_zero (T : ℝ) : zeroCount T = densityCount 0 T := by
  unfold zeroCount densityCount positiveZeroSum
  apply tsum_congr
  intro ρ
  simp only [ρ.property.2.1, true_and]

/-- Every N of t below V is one finite sum over a common actual-zero cutoff. -/
theorem zeroCount_eq_finite {t V : ℝ} (htV : t ≤ V) :
    zeroCount t = ∑ ρ ∈ positiveZerosBelow V,
      if (ρ : ℂ).im < t then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0 := by
  rw [zeroCount_eq_densityCount_zero, densityCount_eq_finite htV]
  apply Finset.sum_congr rfl
  intro ρ _
  simp only [ρ.property.2.1, true_and]

/-- A difference of strict counts counts the half-open ordinate window exactly. -/
theorem zero_window_count {U t V : ℝ} (hUt : U ≤ t) (htV : t ≤ V) :
    zeroCount t - zeroCount U = ∑ ρ ∈ positiveZerosBelow V,
      if U ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im < t then
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0 := by
  rw [zeroCount_eq_finite htV, zeroCount_eq_finite (hUt.trans htV), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases ht : (ρ : ℂ).im < t
  · by_cases hU : (ρ : ℂ).im < U
    · simp [ht, hU, not_le.mpr hU]
    · simp [ht, hU, le_of_not_gt hU]
  · have hU : ¬ (ρ : ℂ).im < U := by intro h; exact ht (h.trans_le hUt)
    simp [ht, hU]

/-- Finite partial summation for N uses the window from U inclusively to V exclusively.
These endpoints match the strict count definition and require no endpoint-zero exclusion. -/
theorem zero_window_partial_summation {U V : ℝ} {φ φ' : ℝ → ℝ}
    (hUV : U ≤ V)
    (hd : ∀ t ∈ Icc U V, HasDerivAt φ (φ' t) t)
    (hi : IntervalIntegrable φ' volume U V) :
    positiveZeroSum (fun ρ => if U ≤ ρ.im ∧ ρ.im < V then φ ρ.im else 0) =
      φ V * zeroCount V - φ U * zeroCount U - ∫ t in U..V, zeroCount t * φ' t := by
  classical
  let s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} :=
    (positiveZerosBelow V).filter (fun ρ => U ≤ (ρ : ℂ).im)
  have hs : ∀ ρ ∈ s, (ρ : ℂ).im ∈ Icc U V := by
    intro ρ hρ
    obtain ⟨hmem, hU⟩ := Finset.mem_filter.mp hρ
    exact ⟨hU, (mem_positiveZerosBelow.mp hmem).2.le⟩
  have hcount : ∀ t ∈ Icc U V, (∑ ρ ∈ s,
      if (ρ : ℂ).im < t then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) =
        zeroCount t - zeroCount U := by
    intro t ht
    rw [zero_window_count ht.1 ht.2, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    split_ifs <;> simp_all
  have htotal : (∑ ρ ∈ s, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)) =
      zeroCount V - zeroCount U := by
    rw [zero_window_count hUV le_rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp [(mem_positiveZerosBelow.mp hρ).2]
  have hsum : positiveZeroSum (fun ρ => if U ≤ ρ.im ∧ ρ.im < V then φ ρ.im else 0) =
      ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * φ (ρ : ℂ).im := by
    rw [positiveZeroSum_eq_finite V _ ?_, Finset.sum_filter]
    · apply Finset.sum_congr rfl
      intro ρ hρ
      have hV := (mem_positiveZerosBelow.mp hρ).2
      by_cases hU : U ≤ (ρ : ℂ).im <;> simp [hU, hV]
    · intro ρ hV
      exact ite_eq_right (by intro h; linarith [h.2])
  have hmain := finite_partial_summation s (fun ρ => (ρ : ℂ).im)
    (fun ρ => (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)) hs hd hi
  have hint : (∫ t in U..V, (∑ ρ ∈ s,
      if (ρ : ℂ).im < t then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) * φ' t) =
      ∫ t in U..V, (zeroCount t - zeroCount U) * φ' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hUV] at ht
    dsimp only
    rw [hcount t ht]
  rw [htotal, hint] at hmain
  have hN : IntervalIntegrable (fun t => zeroCount t * φ' t) volume U V := by
    simpa only [zeroCount_eq_densityCount_zero] using
      densityCount_mul_integrable (σ := 0) hUV hi
  have hconst := hi.const_mul (zeroCount U)
  have hsplit : (∫ t in U..V, (zeroCount t - zeroCount U) * φ' t) =
      (∫ t in U..V, zeroCount t * φ' t) - zeroCount U * (φ V - φ U) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub hN hconst, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd t (by simpa only [uIcc_of_le hUV] using ht)) hi]
  rw [hsplit] at hmain
  rw [hsum, hmain]
  ring

end LeanLab.KadiriLumley2014.Task399
