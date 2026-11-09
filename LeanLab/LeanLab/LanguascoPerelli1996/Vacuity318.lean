import LeanLab.LanguascoPerelli1996.Decomp318a

/-!
Finite witnesses for the hypotheses of P0071 page 355 display 13.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Vacuity318
open Complex Real MeasureTheory Interpolation318

/-- Page 355 display 13, derived finite bound for every symmetric prefix mass. -/
theorem prefix_mass_bound_exists {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ,
      mass s (fun i => if |γ i| ≤ u then c i else 0) γ ≤ M := by
  classical
  refine ⟨∑ t ∈ s.powerset, mass t c γ, Finset.sum_nonneg (fun t _ => mass_nonneg t c γ), ?_⟩
  intro u
  have he : mass s (fun i => if |γ i| ≤ u then c i else 0) γ =
      mass (s.filter (fun i => |γ i| ≤ u)) c γ := by
    unfold mass
    congr 1
    funext v
    have hh : (∑ i ∈ s, (if |γ i| ≤ u then c i else 0) * Complex.exp (Complex.I * γ i * v)) =
        ∑ i ∈ s.filter (fun i => |γ i| ≤ u), c i * Complex.exp (Complex.I * γ i * v) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp
    rw [hh]
  rw [he]
  exact Finset.single_le_sum (fun t _ => mass_nonneg t c γ)
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _))

/-- Page 355 display 13, a genuine finite bound for its entire correlation premise.
No GRH hypothesis is needed for this witness. -/
theorem correlation_bound_exists {X : ℝ} (hX : 0 < X) {U T : ℝ}
    (hU : 0 ≤ U) (hUT : U ≤ T) (q : ℕ) [NeZero q] (a : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M := by
  have hneg : (-1 : ℝ) ≤ T := by linarith
  obtain ⟨ι, s, c, γ, _, _, hp⟩ := Decomp318a.band_prefix_representation hX hneg q a
  obtain ⟨M, hM, hm⟩ := prefix_mass_bound_exists s c γ
  refine ⟨M, hM, ?_⟩
  intro u hUu huT
  have hu : (-1 : ℝ) ≤ u := by linarith
  have he : mass s (fun i => if |γ i| ≤ u then c i else 0) γ = ‖F X u q a‖ := by
    unfold mass
    simp_rw [← hp u hu huT]
    exact Mass108.full_weighted_mass hX u q a
  rw [← he]
  exact hm u

end LeanLab.LanguascoPerelli1996.Vacuity318

#print axioms LeanLab.LanguascoPerelli1996.Vacuity318.prefix_mass_bound_exists
#print axioms LeanLab.LanguascoPerelli1996.Vacuity318.correlation_bound_exists
