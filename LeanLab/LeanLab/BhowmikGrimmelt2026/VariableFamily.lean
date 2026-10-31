/-
A generic obstruction to applying one Fourier coefficient bound to a varying family.
This concerns the existing Parseval question for Lemma 7.3, page 26.
It does not refute that lemma.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ApproximationError
import LeanLab.BhowmikGrimmelt2026.Gallagher

namespace LeanLab.BhowmikGrimmelt2026

/-- Separate unit interval integrals give a bound with a factor equal to the family size. -/
theorem variable_family_card_bound (s : Finset ℕ) (F : ℕ → ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ n ∈ s, ∀ α ∈ Set.Icc (0 : ℝ) 1, ‖F n α‖ ≤ M) :
    ∑ n ∈ s, ‖∫ α in (0 : ℝ)..1, F n α‖ ^ 2 ≤ (s.card : ℝ) * M ^ 2 := by
  calc
    _ ≤ ∑ _n ∈ s, M ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hi : ‖∫ α in (0 : ℝ)..1, F n α‖ ≤ M := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := F n) (a := (0 : ℝ)) (b := 1) (C := M) (by
            intro α hα
            have hα' : α ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hα
            exact hF n hn α ⟨hα'.1.le, hα'.2⟩)
        simpa using h
      exact pow_le_pow_left₀ (norm_nonneg _) hi 2
    _ = (s.card : ℝ) * M ^ 2 := by simp

/-- A separate exponential for each coefficient prevents a bound independent of family size. -/
theorem not_variable_family_unit_bound :
    ¬ (∀ F : ℕ → ℝ → ℂ,
      (∀ n ∈ Finset.Icc 1 2, ∀ α : ℝ, ‖F n α‖ ≤ 1) →
      (∑ n ∈ Finset.Icc 1 2,
        ‖∫ α in (0 : ℝ)..1, F n α * ee (-(n * α))‖ ^ 2) ≤ 1) := by
  intro h
  have hb := h (fun n α => ee (n * α)) (by intro n hn α; rw [norm_ee])
  have hi (n : ℕ) : (∫ α in (0 : ℝ)..1, ee (n * α) * ee (-(n * α))) = 1 := by
    have heq (α : ℝ) : ee (n * α) * ee (-(n * α)) = 1 := by
      rw [ee_mul, add_neg_cancel]
      simp [ee]
    simp_rw [heq]
    simp
  norm_num [hi] at hb

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.variable_family_card_bound
#print axioms LeanLab.BhowmikGrimmelt2026.not_variable_family_unit_bound
