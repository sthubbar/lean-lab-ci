import LeanLab.Pintz2021.TranslatedTask53

/-!
Finite averaging over powers of two for P0054 page 14 displays 4.8 and 4.9.
Ordered exponent tuples retain multiplicity.
This is finite algebra and uses the proved parameter criterion only.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.MultiplePowersTask53

open Finset DivisorSumTask53 TranslatedTask53

attribute [local instance] Classical.propDecidable

/-- The ordered tuples of k exponents in the finite cutoff range. -/
noncomputable def exponentTuples (K k : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun _ : Fin k => Icc 1 K

/-- The sum of the first k powers in an ordered exponent tuple. -/
def partialPowers {k : ℕ} (ν : Fin k → ℕ) : ℕ := ∑ i, 2 ^ ν i

/-- The singular series sum over k fixed coordinates and one varying coordinate. -/
noncomputable def iteratedSingularSum (m q K k : ℕ) : ℝ :=
  ∑ ν ∈ exponentTuples K k,
    ∑ t ∈ eligibleExponents (m - partialPowers ν) q K,
      Sing (m - partialPowers ν - 2 ^ t)

/-- The shifted one-coordinate filter is exactly the full positive difference filter. -/
theorem shifted_exponent_mem_iff {k : ℕ} (m q K t : ℕ) (ν : Fin k → ℕ) :
    t ∈ eligibleExponents (m - partialPowers ν) q K ↔
      t ∈ Icc 1 K ∧ partialPowers ν + 2 ^ t < m ∧
        q ∣ m - (partialPowers ν + 2 ^ t) := by
  have hp : 0 < (2 : ℕ) ^ t := by positivity
  simp only [eligibleExponents, mem_filter, Nat.sub_sub]
  constructor
  · rintro ⟨ht, hpos, hdiv⟩
    exact ⟨ht, by omega, hdiv⟩
  · rintro ⟨ht, hpos, hdiv⟩
    exact ⟨ht, by omega, hdiv⟩

/-- Uniform one-coordinate control gives the finite several-power average. -/
theorem iteratedSingularSum_le_of_parameters (m q K k D : ℕ) {X δ : ℝ}
    (hX : 1 ≤ X) (hm : (m : ℝ) ≤ X) (hK : (K : ℝ) ≤ Real.logb 2 X)
    (hq : Odd q) (hq0 : 0 < q) (hD : 4 ≤ D) (hδ : 0 < δ)
    (hsmall : Real.exp 27 * Real.log D / LeanLab.LPZ2007.xi q ≤ δ)
    (htail : ∑' j, LeanLab.LPZ2007.seriesTerm (j + (D + 1)) ≤ δ)
    (hscale : (6 * Real.exp 27 / δ) ^ 2 + 1 ≤ Real.logb 2 X) :
    iteratedSingularSum m q K k ≤ (K : ℝ) ^ k * (6 * C0 * δ * Real.logb 2 X) := by
  unfold iteratedSingularSum
  calc
    _ ≤ ∑ _ν ∈ exponentTuples K k, 6 * C0 * δ * Real.logb 2 X := by
      apply sum_le_sum
      intro ν _
      have hm' : ((m - partialPowers ν : ℕ) : ℝ) ≤ X := by
        have hsub : ((m - partialPowers ν : ℕ) : ℝ) ≤ m := by
          exact_mod_cast Nat.sub_le m (partialPowers ν)
        exact hsub.trans hm
      exact lemma2_sum_le_of_parameters (m - partialPowers ν) q K D
        hX hm' hK hq hq0 hD hδ hsmall htail hscale
    _ = _ := by simp [exponentTuples, Fintype.card_piFinset, nsmul_eq_mul]

/-- The distinct positive shifted targets satisfying the divisibility filter. -/
noncomputable def eligibleShiftSet (m q K k : ℕ) : Finset ℕ :=
  ((exponentTuples K k).sigma (fun ν => eligibleExponents (m - partialPowers ν) q K)).image
    (fun p => m - partialPowers p.1 - 2 ^ p.2)

/-- Removing repeated targets cannot increase the nonnegative weighted sum. -/
theorem distinct_shift_sum_le_iterated (m q K k : ℕ) :
    ∑ n ∈ eligibleShiftSet m q K k, Sing n ≤ iteratedSingularSum m q K k := by
  unfold eligibleShiftSet
  calc
    _ ≤ ∑ p ∈ (exponentTuples K k).sigma
        (fun ν => eligibleExponents (m - partialPowers ν) q K),
        Sing (m - partialPowers p.1 - 2 ^ p.2) :=
      sum_image_le_of_nonneg (fun n _ => (Applications.Sing_pos n).le)
    _ = iteratedSingularSum m q K k := by
      rw [sum_sigma]
      rfl

end LeanLab.Pintz2021.MultiplePowersTask53

#print axioms LeanLab.Pintz2021.MultiplePowersTask53.shifted_exponent_mem_iff
#print axioms LeanLab.Pintz2021.MultiplePowersTask53.iteratedSingularSum_le_of_parameters
#print axioms LeanLab.Pintz2021.MultiplePowersTask53.distinct_shift_sum_le_iterated
