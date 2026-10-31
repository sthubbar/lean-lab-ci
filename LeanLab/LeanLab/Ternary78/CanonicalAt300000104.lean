import LeanLab.Ternary78.CanonicalGamma104
import LeanLab.Ternary78.BennettAt300000
import LeanLab.Ternary78.BennettThreshold
/-
AI wrote this Lean code. Binary Goldbach is open.
Concrete consequences for actual analytic zeros at conductor 300000.
The analytic input is Bennett Theorem 1.1 on page 2 of arXiv 2005.02989.
-/

namespace LeanLab.Ternary78.Bennett
/-- CONDITIONAL ON BennettThm1_1 for the actual canonical count.
An actual zero occurrence exists through height 5/2 at conductor 300000. -/
theorem actual_zero_grid25_exists (hB : BennettThm1_1 canonicalCount 300000)
    (χ : DirichletCharacter ℂ 300000) (hχ : χ.IsPrimitive) :
    ∃ w : zeroOccurrences χ, |w.val.1.im| ≤ 5 / 2 := by
  have hpos := count_grid25_positive hB χ hχ
  simp only [canonicalCount, show (300000 : ℕ) ≠ 0 by norm_num, dite_false] at hpos
  have hnonempty : Nonempty {w : zeroOccurrences χ // |w.val.1.im| ≤ (5 / 2 : ℝ)} :=
    (Nat.card_pos_iff.mp (by omega : 0 < Nat.card {w : zeroOccurrences χ // |w.val.1.im| ≤ (5 / 2 : ℝ)})).1
  obtain ⟨w⟩ := hnonempty
  exact ⟨w.val, w.property⟩

#print axioms actual_zero_grid25_exists

/-- An unconditional upper bound for the one point gamma certificate.
Mathlib convexity bounds Gamma of 23/8 by 15/8, and two recurrence steps give the result. -/
theorem gamma25_weight_le_three_tenths : ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + ((5 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ (3 / 10 : ℝ) := by
  have hG2 : Real.Gamma (2 : ℝ) = 1 := by
    simp
  have hG3 : Real.Gamma (3 : ℝ) = 2 := by
    simp
  have hG : Real.Gamma (23 / 8 : ℝ) ≤ (15 / 8 : ℝ) := by
    have h := Real.convexOn_Gamma.2
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) (by norm_num : (3 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (0 : ℝ) ≤ 7 / 8)
      (by norm_num : (1 / 8 : ℝ) + 7 / 8 = 1)
    norm_num [smul_eq_mul, hG2, hG3] at h ⊢
    exact h
  have htail := gamma_norm_mul_pow_le_real (by norm_num : (0 : ℝ) < 7 / 8) (5 / 2) 2
  norm_num at htail ⊢
  linarith

#print axioms gamma25_weight_le_three_tenths

/-- CONDITIONAL ON BennettThm1_1 for the actual canonical count.
The convergent real sum of actual gamma zero weights has the positive one point lower bound. -/
theorem actual_gamma25_lower (hB : BennettThm1_1 canonicalCount 300000)
    (χ : DirichletCharacter ℂ 300000) (hχ : χ.IsPrimitive) :
    ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + ((5 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      ∑' w : zeroOccurrences χ,
        ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + (w.val.1.im : ℂ) * Complex.I)‖ := by
  obtain ⟨w, hw⟩ := actual_zero_grid25_exists hB χ hχ
  have hweight := gamma_norm_antitone (by norm_num : (0 : ℝ) < 7 / 8)
    (by change (0 : ℝ) ≤ |w.val.1.im|; exact abs_nonneg _)
    (show (5 / 2 : ℝ) ∈ Set.Ici 0 by norm_num) hw
  dsimp only at hweight
  rw [gamma_norm_abs] at hweight
  have hs := actual_gamma_summable hB le_rfl (by norm_num) χ hχ
    (by norm_num : (0 : ℝ) < 7 / 8)
  exact hweight.trans (hs.le_tsum w (fun _ _ => norm_nonneg _))

#print axioms actual_gamma25_lower

/-- Negative MODEL result. The proved one point lower certificate admits
an S below 0.985 that closes the existing model at its verification endpoint.
This does not say that the actual zero sum is small. -/
theorem gamma25_certificate_has_closing_model : ∃ S : ℝ,
    ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + ((5 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ S ∧
      S < 0.985 ∧ S * Real.sqrt 300000 ≤
        LeanLab.Ternary78.Threshold.m78 * (0.495461 * 8.875e30 : ℝ) ^ (1 / 8 : ℝ) := by
  exact weak_certificate_has_closing_model
    (gamma25_weight_le_three_tenths.trans (by norm_num))

#print axioms gamma25_certificate_has_closing_model

end LeanLab.Ternary78.Bennett
