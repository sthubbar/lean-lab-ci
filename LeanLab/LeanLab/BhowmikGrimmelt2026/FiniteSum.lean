/-
Finite sum bounds used to sum the rational terms in Lemma 7.2, page 26.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ReducedPairs

namespace LeanLab.BhowmikGrimmelt2026

/-- A uniform term bound gives the cardinality times that bound for the sum. -/
theorem norm_sum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℂ) {E : ℝ}
    (h : ∀ i ∈ s, ‖f i‖ ≤ E) : ‖∑ i ∈ s, f i‖ ≤ (s.card : ℝ) * E := by
  calc
    _ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, E := Finset.sum_le_sum h
    _ = (s.card : ℝ) * E := by simp

/-- One exceptional summand and a uniform bound for all other summands. -/
theorem norm_sum_le_one_term {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ)
    {p : ι} (hp : p ∈ s) {D E : ℝ} (hE : 0 ≤ E) (hpD : ‖f p‖ ≤ D)
    (hother : ∀ i ∈ s, i ≠ p → ‖f i‖ ≤ E) :
    ‖∑ i ∈ s, f i‖ ≤ D + (s.card : ℝ) * E := by
  rw [← Finset.add_sum_erase _ _ hp]
  calc
    _ ≤ ‖f p‖ + ‖∑ i ∈ s.erase p, f i‖ := norm_add_le _ _
    _ ≤ D + ((s.erase p).card : ℝ) * E := add_le_add hpD
      (norm_sum_le_card_mul _ _ (fun i hi =>
        hother i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)))
    _ ≤ D + (s.card : ℝ) * E := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast Finset.card_le_card (Finset.erase_subset (a := p) (s := s))

/-- The same bound after subtracting one from the distinguished summand. -/
theorem norm_sum_sub_one_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ)
    {p : ι} (hp : p ∈ s) {D E : ℝ} (hE : 0 ≤ E) (hpD : ‖f p - 1‖ ≤ D)
    (hother : ∀ i ∈ s, i ≠ p → ‖f i‖ ≤ E) :
    ‖(∑ i ∈ s, f i) - 1‖ ≤ D + (s.card : ℝ) * E := by
  have heq : (∑ i ∈ s, f i) - 1 = (f p - 1) + ∑ i ∈ s.erase p, f i := by
    rw [← Finset.add_sum_erase _ _ hp]
    ring
  rw [heq]
  calc
    _ ≤ ‖f p - 1‖ + ‖∑ i ∈ s.erase p, f i‖ := norm_add_le _ _
    _ ≤ D + ((s.erase p).card : ℝ) * E := add_le_add hpD
      (norm_sum_le_card_mul _ _ (fun i hi =>
        hother i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)))
    _ ≤ D + (s.card : ℝ) * E := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast Finset.card_le_card (Finset.erase_subset (a := p) (s := s))

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.norm_sum_le_card_mul
#print axioms LeanLab.BhowmikGrimmelt2026.norm_sum_le_one_term
#print axioms LeanLab.BhowmikGrimmelt2026.norm_sum_sub_one_le
