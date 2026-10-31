import LeanLab.Pintz2021.DecompJ281

/-!
Finite bookkeeping for P0054 page 8 display 2.22.
Both height restrictions, the lcm restriction and the character cutoff are retained.
The analytic rate for the discarded terms remains a separate input.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.Truncation168

open State1581 DecompJ281 Finset

attribute [local instance] Classical.propDecidable

/-- The exact retained pairs in display 2.22 for the difference problem. -/
noncomputable def retainedPairs (E : Finset ExcPair) (P U : ℝ) (m : ℕ) :
    Finset (ExcPair × ExcPair) :=
  (E ×ˢ E).filter fun p => |p.1.ρ.im| ≤ U ∧ |p.2.ρ.im| ≤ U ∧
    (Nat.lcm p.1.r p.2.r : ℝ) ≤ P ∧ UCutoff p.1 p.2 m ≤ U

/-- One term of the multiplicity weighted difference main sum. -/
noncomputable def pairTerm (Sg : ExcPair → ExcPair → ℕ → ℂ)
    (ε X : ℝ) (m : ℕ) (p : ExcPair × ExcPair) : ℂ :=
  ((mult p.1 * mult p.2 : ℕ) : ℂ) * (Asign p.1 : ℂ) * (Asign p.2 : ℂ) *
    Sg p.1 p.2 m *
      WeightedKernelsTask08.weightedKernel (X1 ε X) X p.1.ρ p.2.ρ m true

/-- The finite truncated main sum with every restriction of display 2.22. -/
noncomputable def truncatedPrime (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P U : ℝ) (m : ℕ) : ℂ :=
  ∑ p ∈ retainedPairs E P U m, pairTerm Sg ε X m p

/-- Membership exposes both heights, the lcm and the character cutoff. -/
theorem mem_retainedPairs {E : Finset ExcPair} {P U : ℝ} {m : ℕ}
    {z w : ExcPair} :
    (z, w) ∈ retainedPairs E P U m ↔ z ∈ E ∧ w ∈ E ∧
      |z.ρ.im| ≤ U ∧ |w.ρ.im| ≤ U ∧ (Nat.lcm z.r w.r : ℝ) ≤ P ∧
        UCutoff z w m ≤ U := by
  simp [retainedPairs, and_assoc]

/-- Increasing the cutoff retains every pair already present. -/
theorem retainedPairs_mono {E : Finset ExcPair} {P U V : ℝ} {m : ℕ} (hUV : U ≤ V) :
    retainedPairs E P U m ⊆ retainedPairs E P V m := by
  intro p hp
  obtain ⟨hz, hw, hγz, hγw, hl, hc⟩ := mem_retainedPairs.mp hp
  exact mem_retainedPairs.mpr ⟨hz, hw, hγz.trans hUV, hγw.trans hUV, hl, hc.trans hUV⟩

/-- The pole pair survives when both the arc level and cutoff are at least one. -/
theorem pole_pair_retained {E : Finset ExcPair} (hp : pole ∈ E) {P U : ℝ}
    (hP : 1 ≤ P) (hU : 1 ≤ U) (m : ℕ) :
    (pole, pole) ∈ retainedPairs E P U m := by
  apply mem_retainedPairs.mpr
  refine ⟨hp, hp, ?_, ?_, ?_, pole_not_truncated hU⟩
  · simpa [pole] using (zero_le_one.trans hU)
  · simpa [pole] using (zero_le_one.trans hU)
  · simpa [pole] using hP

/-- A finite exceptional set turns the existing mainTermPrime into a finite pair sum. -/
theorem mainTermPrime_eq_sum (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X : ℝ) (m : ℕ) :
    mainTermPrime (E : Set ExcPair) Sg ε X m =
      ∑ p ∈ E ×ˢ E, pairTerm Sg ε X m p := by
  simp only [mainTermPrime, finsum_mem_coe_finset, sum_product, pairTerm]

/-- The full main sum splits exactly into retained and discarded pairs. -/
theorem main_partition (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P U : ℝ) (m : ℕ) :
    mainTermPrime (E : Set ExcPair) Sg ε X m =
      truncatedPrime E Sg ε X P U m +
        ∑ p ∈ (E ×ˢ E) \ retainedPairs E P U m, pairTerm Sg ε X m p := by
  rw [mainTermPrime_eq_sum, truncatedPrime]
  simpa only [add_comm] using
    (sum_sdiff (f := pairTerm Sg ε X m)
      (show retainedPairs E P U m ⊆ E ×ˢ E from filter_subset _ _)).symm

/-- The norm of the truncation error is at most the sum of discarded term norms. -/
theorem norm_truncation_error_le (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P U : ℝ) (m : ℕ) :
    ‖mainTermPrime (E : Set ExcPair) Sg ε X m - truncatedPrime E Sg ε X P U m‖ ≤
      ∑ p ∈ (E ×ˢ E) \ retainedPairs E P U m, ‖pairTerm Sg ε X m p‖ := by
  rw [main_partition E Sg ε X P U m, add_sub_cancel_left]
  exact norm_sum_le _ _

/-- Above a finite threshold all pairs survive if their lcm levels are permitted. -/
theorem eventually_all_retained (E : Finset ExcPair) (P : ℝ) (m : ℕ)
    (hP : ∀ z ∈ E, ∀ w ∈ E, (Nat.lcm z.r w.r : ℝ) ≤ P) :
    ∃ U0 : ℝ, 2 ≤ U0 ∧ ∀ U : ℝ, U0 ≤ U → retainedPairs E P U m = E ×ˢ E := by
  let F : ExcPair × ExcPair → ℝ := fun p =>
    max (max |p.1.ρ.im| |p.2.ρ.im|) (UCutoff p.1 p.2 m)
  obtain ⟨B, hB⟩ := ((E ×ˢ E).finite_toSet.image F).bddAbove
  refine ⟨max B 2, le_max_right _ _, fun U hU => ?_⟩
  apply Subset.antisymm (filter_subset _ _) ?_
  intro p hp
  obtain ⟨hz, hw⟩ := mem_product.mp hp
  have hb : F p ≤ U :=
    (hB (Set.mem_image_of_mem F hp)).trans ((le_max_left _ _).trans hU)
  have hb' := max_le_iff.mp hb
  exact mem_retainedPairs.mpr
    ⟨hz, hw, (max_le_iff.mp hb'.1).1, (max_le_iff.mp hb'.1).2,
      hP _ hz _ hw, hb'.2⟩

/-- A discarded pair is bounded by its multiplicity, series norm and the cutoff X. -/
theorem norm_pairTerm_le (Sg : ExcPair → ExcPair → ℕ → ℂ)
    (ε : ℝ) {X : ℝ} (hX : 0 ≤ X) (m : ℕ) (z w : ExcPair)
    (hz : z.ρ.re ≤ 1) (hw : w.ρ.re ≤ 1) :
    ‖pairTerm Sg ε X m (z, w)‖ ≤
      ((mult z * mult w : ℕ) : ℝ) * ‖Sg z w m‖ * X := by
  have hA : ∀ v : ExcPair, |Asign v| = 1 := by
    intro v
    unfold Asign
    split_ifs <;> norm_num
  simp only [pairTerm, norm_mul, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, hA, mul_one]
  exact mul_le_mul_of_nonneg_left
    (WeightedKernelsTask08.norm_weightedKernel_le_X (X1 ε X) hX hz hw m true)
      (by positivity)

/-- The finite error is controlled by the multiplicity weighted discarded series mass. -/
theorem norm_truncation_error_le_mass (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε : ℝ) {X : ℝ} (hX : 0 ≤ X)
    (P U : ℝ) (m : ℕ) (hρ : ∀ z ∈ E, z.ρ.re ≤ 1) :
    ‖mainTermPrime (E : Set ExcPair) Sg ε X m - truncatedPrime E Sg ε X P U m‖ ≤
      X * ∑ p ∈ (E ×ˢ E) \ retainedPairs E P U m,
        ((mult p.1 * mult p.2 : ℕ) : ℝ) * ‖Sg p.1 p.2 m‖ := by
  calc
    _ ≤ ∑ p ∈ (E ×ˢ E) \ retainedPairs E P U m, ‖pairTerm Sg ε X m p‖ :=
      norm_truncation_error_le E Sg ε X P U m
    _ ≤ ∑ p ∈ (E ×ˢ E) \ retainedPairs E P U m,
        ((mult p.1 * mult p.2 : ℕ) : ℝ) * ‖Sg p.1 p.2 m‖ * X := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hz, hw⟩ := mem_product.mp (mem_sdiff.mp hp).1
      exact norm_pairTerm_le Sg ε hX m p.1 p.2 (hρ _ hz) (hρ _ hw)
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro p _; ring

end LeanLab.Pintz2021.Truncation168

#print axioms LeanLab.Pintz2021.Truncation168.mem_retainedPairs
#print axioms LeanLab.Pintz2021.Truncation168.retainedPairs_mono
#print axioms LeanLab.Pintz2021.Truncation168.pole_pair_retained
#print axioms LeanLab.Pintz2021.Truncation168.mainTermPrime_eq_sum
#print axioms LeanLab.Pintz2021.Truncation168.main_partition
#print axioms LeanLab.Pintz2021.Truncation168.norm_truncation_error_le
#print axioms LeanLab.Pintz2021.Truncation168.eventually_all_retained

#print axioms LeanLab.Pintz2021.Truncation168.norm_pairTerm_le
#print axioms LeanLab.Pintz2021.Truncation168.norm_truncation_error_le_mass
