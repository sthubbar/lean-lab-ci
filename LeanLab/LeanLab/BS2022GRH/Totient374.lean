/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Finite double weight reduction for journal p. 1224 display 13. -/
import LeanLab.BS2022GRH.Decomp374f

namespace LeanLab.BS2022GRH.Totient374
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The double squarefree weight follows from the existing single sum input, display 13.
CONDITIONAL ON the explicit Ramare estimate hphi. The proof is finite bookkeeping. -/
theorem small_totient_mass_of_phi (hphi : PaperInputs148.Lemma5PhiJ)
    (D D₀ : ℝ) (a : ℤ) (hD : 1 < D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) :
    (∑ r ∈ (conductors D a).filter (fun r : ℕ => (r : ℝ) ≤ D₀),
      (r.totient : ℝ)⁻¹ * ∑ s ∈ moduli (D / r) a, (s.totient : ℝ)⁻¹) ≤
      Mphi D₀ * Mphi D * log D ^ 2 := by
  let T := (conductors D a).filter (fun r : ℕ => (r : ℝ) ≤ D₀)
  have hbound (S : Finset ℕ) (x : ℝ) (hx : 1 < x)
      (hS : S ⊆ (Icc 1 ⌊x⌋₊).filter (fun s => Squarefree s)) :
      (∑ s ∈ S, (s.totient : ℝ)⁻¹) ≤ Mphi x * log x := by
    apply (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
    simpa only [one_div] using hphi x hx
  have ht : (∑ r ∈ T, (r.totient : ℝ)⁻¹) ≤ Mphi D₀ * log D₀ := by
    apply hbound T D₀ hD₀
    intro r hr
    obtain ⟨hrmem, hrD⟩ := mem_filter.mp hr
    obtain ⟨hrI, hrSF, _⟩ := mem_filter.mp hrmem
    have hr3 : 3 ≤ r := (mem_Ico.mp hrI).1
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, Nat.le_floor hrD⟩, hrSF⟩
  have hs : (∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹) ≤ Mphi D * log D := by
    apply hbound (moduli D a) D hD
    intro s hs
    obtain ⟨hsI, hsSF, _⟩ := mem_filter.mp hs
    obtain ⟨hs1, hsU⟩ := mem_Ico.mp hsI
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hs1, Nat.le_floor (Nat.lt_ceil.mp hsU).le⟩, hsSF⟩
  have hlog0 : 0 ≤ log D₀ := (log_pos hD₀).le
  have hlogD : 0 ≤ log D := (log_pos hD).le
  have hphi0 : 0 ≤ Mphi D₀ := by unfold Mphi; positivity
  have hphiD : 0 ≤ Mphi D := by unfold Mphi; positivity
  have hlog : log D₀ ≤ log D := log_le_log (by linarith) hD₀D
  calc
    (∑ r ∈ T, (r.totient : ℝ)⁻¹ * ∑ s ∈ moduli (D / r) a, (s.totient : ℝ)⁻¹)
        ≤ (∑ r ∈ T, (r.totient : ℝ)⁻¹) * ∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹ := by
      rw [sum_mul]
      apply sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hr3 : 3 ≤ r := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hr).1).1).1
      exact sum_le_sum_of_subset_of_nonneg
        (Decomp374f.cofactor_subset D a r (by linarith) (by omega)) (fun _ _ _ => by positivity)
    _ ≤ (Mphi D₀ * log D₀) * (Mphi D * log D) :=
      mul_le_mul ht hs (sum_nonneg (fun _ _ => by positivity)) (mul_nonneg hphi0 hlog0)
    _ ≤ Mphi D₀ * Mphi D * log D ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hphi0 hphiD) hlogD)
      nlinarith only [hh]

end
end LeanLab.BS2022GRH.Totient374
#print axioms LeanLab.BS2022GRH.Totient374.small_totient_mass_of_phi
