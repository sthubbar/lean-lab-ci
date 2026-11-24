/-
PROVED leaf `leaf_err_coeff_bound` of SPLIT_Decomp409b, P0069 page 27 lines 11 and 12: the
coefficients of the modified M1 N L satisfy (3.1) with B' = 2|B| + 3, using psiErr l at most tau l.
Restated verbatim as `leaf_err_coeff_bound_proof`. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.PROVED_leaf_trunc_coeff_bound

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Decomp1518
attribute [local instance] Classical.propDecidable

theorem psiErr_le {l : ℕ} (hl : l ≠ 0) (w γ : ℝ) : psiErr l w γ ≤ tau l := by
  unfold psiErr; rw [tau_eq_card]
  exact_mod_cast Finset.card_le_card fun d hd => by
    simp only [mem_filter] at hd; simp [hd.2.1, hl]

theorem psiErr_nonneg (l : ℕ) (w γ : ℝ) : 0 ≤ psiErr l w γ := by
  unfold psiErr; positivity

/-- `leaf_err_coeff_bound`, verbatim, proved. -/
theorem leaf_err_coeff_bound_proof (B : ℝ) : ∃ B' : ℝ, ∀ (a b : ℕ → ℂ) (M N w γ : ℝ),
    (∀ k, ‖a k‖ ≤ tau k ^ B) → (∀ k, ‖b k‖ ≤ tau k ^ B) →
    ∀ k : ℕ, ‖(if k = 0 then (0 : ℂ) else ((conv2E a b M N w γ k : ℝ) : ℂ))‖ ≤ tau k ^ B' := by
  refine ⟨2 * |B| + 3, fun a b M N w γ ha hb k => ?_⟩
  by_cases hk : k = 0
  · subst hk
    simp only [ite_true, norm_zero]
    rw [tau_eq_card]; simp only [Nat.divisors_zero, card_empty, Nat.cast_zero]
    rw [Real.zero_rpow (by positivity)]
  rw [if_neg hk, Complex.norm_real, Real.norm_eq_abs]
  have hnn : 0 ≤ conv2E a b M N w γ k := by
    unfold conv2E
    refine sum_nonneg fun m _ => sum_nonneg fun n _ => ?_
    split_ifs
    · exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (psiErr_nonneg _ _ _)
    · exact le_rfl
  rw [abs_of_nonneg hnn]
  unfold conv2E
  refine dsum_le hk M N B _ fun m n hmn => ?_
  have hl : k / (m * n) ≠ 0 := by
    intro h; rcases hmn with ⟨c, hc⟩
    have hmn0 : m * n ≠ 0 := by rintro h0; rw [h0, zero_mul] at hc; exact hk hc
    rw [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hmn0)] at h
    exact hk (by rw [hc, h, mul_zero])
  exact triple_le (one_le_tau hk) (norm_nonneg _) (norm_nonneg _) (psiErr_nonneg _ _ _)
    (coef_le ha (Dvd.dvd.trans (Dvd.intro _ rfl) hmn) hk)
    (coef_le hb (Dvd.dvd.trans (Dvd.intro_left _ rfl) hmn) hk)
    ((psiErr_le hl w γ).trans (tau_mono (Nat.div_dvd_of_dvd hmn) hk))

#print axioms leaf_err_coeff_bound_proof

end LeanLab.BakerHarmanPintz1997.Decomp409b
