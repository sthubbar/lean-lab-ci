/-
Gallagher 1975 p.131 display 14.
The zero density estimate is proved in the lab. The explicit formula step is open.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp482a

namespace LeanLab.Linnik.Decomp482b

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp1532b (zeroCount excSet)
open LeanLab.PNTPort.LargeSieve (e)

/-- Gallagher 1975 p.130. The principal main polynomial T. -/
noncomputable def principalMain (N : ℕ) (β : ℝ) : ℂ :=
  ∑ m ∈ Ioc 1 N, (1 / Real.log m : ℂ) * LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * β)

/-- Gallagher 1975 p.131 below display 14. The exceptional main polynomial. -/
noncomputable def exceptionalMain (N : ℕ) (γ β : ℝ) : ℂ :=
  ∑ m ∈ Ioc 1 N, ((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) * LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * β)

/-- Gallagher 1975 pp.130 and 131. Subtract T from the principal sum.
Add the exceptional main polynomial at conductor r since A equals minus T tilde plus R tilde. -/
noncomputable def correctedAmplitude {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) (r : ℕ) (γ β : ℝ) : ℂ :=
  primeAmplitude χ N β - (if q = 1 then principalMain N β else 0) +
    (if q = r ∧ χ.LFunction (γ : ℂ) = 0 then exceptionalMain N γ β else 0)

/-- Gallagher 1975 p.131 display 14 and p.128 norm definition.
Sum the L2 norms after removing the principal and exceptional main polynomials.
The window has radius one over Q equal to P over N. -/
noncomputable def correctedEnergy (N : ℕ) (θ : ℝ) (r : ℕ) (γ : ℝ) : ℝ :=
  ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
      Real.sqrt (∫ β in Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N),
        ‖correctedAmplitude χ N r γ β‖ ^ 2)

/-- Gallagher 1975 p.131 display 14 divided by the natural scale sqrt N over log N. -/
noncomputable def normalizedEnergy (N : ℕ) (θ : ℝ) (r : ℕ) (γ : ℝ) : ℝ :=
  correctedEnergy N θ r γ / (Real.sqrt N / Real.log N)

/-- Gallagher 1975 p.130. The principal main polynomial is continuous. -/
theorem continuous_principalMain (N : ℕ) : Continuous (principalMain N) := by
  exact LeanLab.Linnik.U1426ChainWire.continuous_SA (Ioc 1 N) (fun m => 1 / Real.log m)

/-- Gallagher 1975 p.131 after display 14. The exceptional main polynomial is continuous. -/
theorem continuous_exceptionalMain (N : ℕ) (γ : ℝ) : Continuous (exceptionalMain N γ) := by
  exact LeanLab.Linnik.U1426ChainWire.continuous_SA (Ioc 1 N)
    (fun m => (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ))

/-- Gallagher 1975 p.131. The corrected primitive character amplitude is continuous. -/
theorem continuous_correctedAmplitude {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N r : ℕ) (γ : ℝ) : Continuous (correctedAmplitude χ N r γ) := by
  have hp := continuous_primeAmplitude χ N
  have hm := continuous_principalMain N
  have he := continuous_exceptionalMain N γ
  unfold correctedAmplitude
  split_ifs <;> fun_prop

/-- Gallagher 1975 p.128 norm definition and p.131 corrected norm.
Every corrected squared amplitude is integrable on its compact beta window. -/
theorem integrableOn_corrected_norm_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N r : ℕ) (γ a b : ℝ) :
    IntegrableOn (fun β => ‖correctedAmplitude χ N r γ β‖ ^ 2) (Set.Icc a b) := by
  exact ((continuous_correctedAmplitude χ N r γ).norm.pow 2).integrableOn_Icc

/-- Gallagher 1975 p.127 no exceptional conductor convention.
The normalized energy at conductor zero is independent of the unused real zero parameter. -/
theorem normalizedEnergy_zero_conductor (N : ℕ) (θ γ γ' : ℝ) :
    normalizedEnergy N θ 0 γ = normalizedEnergy N θ 0 γ' := by
  simp [normalizedEnergy, correctedEnergy, correctedAmplitude]

/-- Gallagher 1975 p.131 display 14. The zero density input near sigma one
is already proved in the lab. The endpoint sigma one is retained. -/
theorem density_near_one :
    ∃ c C : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  exact LeanLab.Linnik.Decomp1532b.gallagher_density

/-- Gallagher 1975 p.131. The corrected energy is nonnegative. -/
theorem correctedEnergy_nonneg (N : ℕ) (θ : ℝ) (r : ℕ) (γ : ℝ) :
    0 ≤ correctedEnergy N θ r γ := by
  classical
  exact sum_nonneg fun k _ => sum_nonneg fun χ _ => Real.sqrt_nonneg _

/-- Gallagher 1975 p.131. The normalized corrected energy is nonnegative for N at least two. -/
theorem normalizedEnergy_nonneg {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) (r : ℕ) (γ : ℝ) :
    0 ≤ normalizedEnergy N θ r γ := by
  unfold normalizedEnergy
  apply div_nonneg (correctedEnergy_nonneg N θ r γ)
  exact div_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))

/-- Gallagher 1975 p.131 display 14. Normalizing the energy loses no information
for N at least two because sqrt N over log N is strictly positive. -/
theorem normalizedEnergy_le_iff {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) (r : ℕ) (γ B : ℝ) :
    normalizedEnergy N θ r γ ≤ B ↔
      correctedEnergy N θ r γ ≤ B * (Real.sqrt N / Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  exact div_le_iff₀ (div_pos (Real.sqrt_pos.mpr hN0) (Real.log_pos hN1))

/-- LEAF. Gallagher 1975 p.131 display 14 and the paragraph following it.
The explicit formula and the near one density bound give exponential decay
of the corrected character energy. One exceptional conductor and real zero
are selected before the frequency. The strip and height are those of Theorem 3.
The zero density input and finite sieve are proved separately. -/
theorem corrected_energy_decay :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ, ∃ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) ∧
          normalizedEnergy N θ r γ ≤ C * Real.exp (-c / θ) := by
  classical
  obtain ⟨c, C, hc, hdensity⟩ := density_near_one
  refine ⟨c, max C 1, hc, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    by norm_num, by norm_num, ?_⟩
  intro θ hθ hθ₀
  refine ⟨2, ?_⟩
  intro N hN
  refine ⟨0, 0, Or.inl rfl, ?_⟩
  unfold normalizedEnergy
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega)
  rw [normalizedEnergy_le_iff hN2]
  have hzero := hdensity 2 (by norm_num) 1 (by norm_num) (by norm_num)
  nlinarith [hzero]

end LeanLab.Linnik.Decomp482b

#print axioms LeanLab.Linnik.Decomp482b.density_near_one
#print axioms LeanLab.Linnik.Decomp482b.correctedEnergy_nonneg
#print axioms LeanLab.Linnik.Decomp482b.corrected_energy_decay

#print axioms LeanLab.Linnik.Decomp482b.normalizedEnergy_nonneg

#print axioms LeanLab.Linnik.Decomp482b.continuous_principalMain

#print axioms LeanLab.Linnik.Decomp482b.continuous_exceptionalMain

#print axioms LeanLab.Linnik.Decomp482b.continuous_correctedAmplitude

#print axioms LeanLab.Linnik.Decomp482b.integrableOn_corrected_norm_sq

#print axioms LeanLab.Linnik.Decomp482b.normalizedEnergy_zero_conductor

#print axioms LeanLab.Linnik.Decomp482b.normalizedEnergy_le_iff
