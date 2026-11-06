/-
P0059 page 5 Section 2.5 and page 7 Lemma 2.5.
Source 4, arXiv 1310.6374 page 9 uses the zero count as a step function.
A finite common cutoff permits an exact step-integral identity without an infinite interchange.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroStep399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory
open Task259

/-- Actual positive-ordinate open-strip zeros strictly below a fixed height. -/
noncomputable def positiveZerosBelow (V : ℝ) :
    Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} := by
  classical
  let A := {ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} |
    0 < (ρ : ℂ).im ∧ (ρ : ℂ).im < V}
  have hfin := Set.Finite.preimage
    (f := (Subtype.val : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} → ℂ))
    Subtype.val_injective.injOn (finite_strip_zeros_height V)
  have hA : A.Finite := hfin.subset (by
    intro ρ hρ
    exact ⟨ρ.property.1, ρ.property.2.1, ρ.property.2.2, hρ.1, hρ.2.le⟩)
  exact hA.toFinset

/-- Membership in the finite cutoff uses the same strict upper height as N of T. -/
theorem mem_positiveZerosBelow {V : ℝ}
    {ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}} :
    ρ ∈ positiveZerosBelow V ↔ 0 < (ρ : ℂ).im ∧ (ρ : ℂ).im < V := by
  classical
  simp [positiveZerosBelow]

/-- A bounded positive-ordinate sum is an exact finite sum over one common cutoff. -/
theorem positiveZeroSum_eq_finite (V : ℝ) (f : ℂ → ℝ)
    (hcut : ∀ ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
      V ≤ (ρ : ℂ).im → f ρ = 0) :
    positiveZeroSum f = ∑ ρ ∈ positiveZerosBelow V,
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * f ρ := by
  classical
  unfold positiveZeroSum
  rw [tsum_eq_sum (s := positiveZerosBelow V) ?_]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [ite_eq_left (mem_positiveZerosBelow.mp hρ).1]
  · intro ρ hρ
    by_cases hp : 0 < (ρ : ℂ).im
    · have hV : V ≤ (ρ : ℂ).im := by
        by_contra h
        exact hρ (mem_positiveZerosBelow.mpr ⟨hp, lt_of_not_ge h⟩)
      simp [hp, hcut ρ hV]
    · simp [hp]

/-- Every density count below V is a finite step sum over the same fixed set of zeros. -/
theorem densityCount_eq_finite {t V : ℝ} (htV : t ≤ V) (σ : ℝ) :
    densityCount σ t = ∑ ρ ∈ positiveZerosBelow V,
      if σ < (ρ : ℂ).re ∧ (ρ : ℂ).im < t then
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0 := by
  classical
  unfold densityCount
  rw [positiveZeroSum_eq_finite V _ ?_]
  · apply Finset.sum_congr rfl
    intro ρ _
    split_ifs <;> simp
  · intro ρ hV
    exact ite_eq_right (by intro h; linarith [h.2])

/-- Verified RH through H makes the density count zero there when sigma exceeds one half. -/
theorem densityCount_eq_zero_of_verified {H σ T : ℝ}
    (hRH : VerifiedHeight H) (hσ : 1 / 2 < σ) (hT : T ≤ H) :
    densityCount σ T = 0 := by
  unfold densityCount positiveZeroSum
  calc
    _ = ∑' _ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}, (0 : ℝ) := by
      apply tsum_congr
      intro ρ
      by_cases hp : 0 < (ρ : ℂ).im
      · rw [ite_eq_left hp]
        by_cases h : σ < (ρ : ℂ).re ∧ (ρ : ℂ).im < T
        · have hre := hRH ρ ρ.property.1 ρ.property.2.1.le ρ.property.2.2.le
            hp.le (h.2.le.trans hT)
          linarith [h.1]
        · simp [h]
      · simp [hp]
    _ = 0 := tsum_zero

/-- Finite density partial summation with strict upper cutoff.
This is the exact finite step preceding the infinite Stieltjes identity on cited page 9.
CONDITIONAL ON the displayed verified-height hypothesis. -/
theorem density_partial_summation {H V σ : ℝ} {φ φ' : ℝ → ℝ}
    (hHV : H ≤ V) (hσ : 1 / 2 < σ) (hRH : VerifiedHeight H)
    (hd : ∀ t ∈ Icc H V, HasDerivAt φ (φ' t) t)
    (hi : IntervalIntegrable φ' volume H V) :
    positiveZeroSum (fun ρ => if σ < ρ.re ∧ ρ.im < V then φ ρ.im else 0) =
      φ V * densityCount σ V - ∫ t in H..V, densityCount σ t * φ' t := by
  classical
  let s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} :=
    (positiveZerosBelow V).filter (fun ρ => σ < (ρ : ℂ).re)
  have hs : ∀ ρ ∈ s, (ρ : ℂ).im ∈ Icc H V := by
    intro ρ hρ
    obtain ⟨hmem, hre⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hp, hV⟩ := mem_positiveZerosBelow.mp hmem
    refine ⟨?_, hV.le⟩
    by_contra h
    have hr := hRH ρ ρ.property.1 ρ.property.2.1.le ρ.property.2.2.le
      hp.le (lt_of_not_ge h).le
    linarith
  have hcount : ∀ t ∈ Icc H V,
      (∑ ρ ∈ s, if (ρ : ℂ).im < t then
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) = densityCount σ t := by
    intro t ht
    rw [densityCount_eq_finite ht.2, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    split_ifs <;> simp_all
  have htotal : (∑ ρ ∈ s, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)) =
      densityCount σ V := by
    rw [densityCount_eq_finite le_rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hV := (mem_positiveZerosBelow.mp hρ).2
    simp [hV]
  have hsum : positiveZeroSum (fun ρ => if σ < ρ.re ∧ ρ.im < V then φ ρ.im else 0) =
      ∑ ρ ∈ s, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * φ (ρ : ℂ).im := by
    rw [positiveZeroSum_eq_finite V _ ?_, Finset.sum_filter]
    · apply Finset.sum_congr rfl
      intro ρ hρ
      have hV := (mem_positiveZerosBelow.mp hρ).2
      by_cases hr : σ < (ρ : ℂ).re <;> simp [hr, hV]
    · intro ρ hV
      exact ite_eq_right (by intro h; linarith [h.2])
  rw [hsum, finite_partial_summation s (fun ρ => (ρ : ℂ).im)
    (fun ρ => (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)) hs hd hi, htotal]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hHV] at ht
  dsimp only
  rw [hcount t ht]

end LeanLab.KadiriLumley2014.Task399
