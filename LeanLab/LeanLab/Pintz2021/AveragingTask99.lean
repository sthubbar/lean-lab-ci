import LeanLab.Pintz2021.Lemma2Task99
import LeanLab.Pintz2021.MultiplePowersTask53

/-!
P0054 page 14, the paragraph between displays 4.8 and 4.9.
The proved Lemma 2 controls the last coordinate uniformly in the earlier powers.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.AveragingTask99

open Finset DivisorSumTask53 MultiplePowersTask53 Lemma2Task99

/-- The several-power weighted average with the paper's original cutoff. -/
theorem iterated_average {η : ℝ} (hη : 0 < η) :
    ∃ Cη : ℝ, ∀ (X : ℝ) (m q k : ℕ), (m : ℝ) ≤ X → Odd q → Squarefree q →
      Cη < min (q : ℝ) X →
      iteratedSingularSum m q ⌊Lnu X⌋₊ k ≤
        (⌊Lnu X⌋₊ : ℝ) ^ k * (η * Lnu X) := by
  obtain ⟨Cη, hCη⟩ := lemma2_proved η hη
  refine ⟨Cη, fun X m q k hm hq hsq hlarge => ?_⟩
  unfold iteratedSingularSum
  calc
    _ ≤ ∑ _ν ∈ exponentTuples ⌊Lnu X⌋₊ k, η * Lnu X := by
      apply sum_le_sum
      intro ν _
      have hm' : ((m - partialPowers ν : ℕ) : ℝ) ≤ X := by
        have hsub : ((m - partialPowers ν : ℕ) : ℝ) ≤ m := by
          exact_mod_cast Nat.sub_le m (partialPowers ν)
        exact hsub.trans hm
      exact hCη X (m - partialPowers ν) q hm' hq hsq hlarge
    _ = _ := by simp [exponentTuples, Fintype.card_piFinset, nsmul_eq_mul]

/-- The same bound holds for distinct positive translated targets. -/
theorem distinct_average {η : ℝ} (hη : 0 < η) :
    ∃ Cη : ℝ, ∀ (X : ℝ) (m q k : ℕ), (m : ℝ) ≤ X → Odd q → Squarefree q →
      Cη < min (q : ℝ) X →
      ∑ n ∈ eligibleShiftSet m q ⌊Lnu X⌋₊ k, Sing n ≤
        (⌊Lnu X⌋₊ : ℝ) ^ k * (η * Lnu X) := by
  obtain ⟨Cη, hCη⟩ := iterated_average hη
  exact ⟨Cη, fun X m q k hm hq hsq hlarge =>
    (distinct_shift_sum_le_iterated m q ⌊Lnu X⌋₊ k).trans
      (hCη X m q k hm hq hsq hlarge)⟩

end LeanLab.Pintz2021.AveragingTask99

#print axioms LeanLab.Pintz2021.AveragingTask99.iterated_average

#print axioms LeanLab.Pintz2021.AveragingTask99.distinct_average
