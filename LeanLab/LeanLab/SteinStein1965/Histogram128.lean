/-
AI wrote this Lean code for CODEX task128.
P0073, equations 4.1 and 4.2, pages 431 and 432.
These identities concern any supplied finite basis. Goldbach is open.
-/
import LeanLab.SteinStein1965.Frequency

namespace LeanLab.SteinStein1965

/-- Equation 4.2 is the histogram of the decomposition counts in equation 4.1. -/
theorem sigma_eq_count (bs : List ℕ) (k x : ℕ) :
    sigma bs k x = ((evensIn 2 x).map (nu bs)).count k := by
  rw [sigma, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  rfl

/-- Equation 4.2 partitions all positive even targets through x by their counts. -/
theorem sum_sigma_support (bs : List ℕ) (x : ℕ) :
    ∑ k ∈ ((evensIn 2 x).map (nu bs)).toFinset, sigma bs k x = (evensIn 2 x).length := by
  simp_rw [sigma_eq_count]
  exact (List.sum_toFinset_count_eq_length ((evensIn 2 x).map (nu bs))).trans (List.length_map ..)

/-- Equations 4.1 and 4.2: no target has count zero exactly when the list is a basis. -/
theorem sigma_zero_iff_basis (bs : List ℕ) (x : ℕ) :
    sigma bs 0 x = 0 ↔ IsBasisFor bs 2 x := by
  rw [basis_iff_nu_pos]
  simp only [sigma, List.length_eq_zero_iff, List.filter_eq_nil_iff, beq_iff_eq]
  constructor
  · intro h m he hlo hhi
    exact Nat.pos_of_ne_zero (h m (mem_evensIn.mpr ⟨hlo, hhi, he⟩))
  · intro h m hm
    obtain ⟨hlo, hhi, he⟩ := mem_evensIn.mp hm
    exact Nat.ne_of_gt (h m he hlo hhi)

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.sigma_eq_count
#print axioms LeanLab.SteinStein1965.sum_sigma_support
#print axioms LeanLab.SteinStein1965.sigma_zero_iff_basis
