import LeanLab.Ternary78.GammaWeights

/-
AI wrote this Lean code. Binary Goldbach is open.
Elementary Gamma tail bounds from the recurrence and the proved height monotonicity.
These do not assume a numerical Gamma or Stirling estimate.
-/

namespace LeanLab.Ternary78.Bennett
open Real Complex

/-- The real Gamma value bounds the norm on its vertical line. -/
theorem gamma_norm_le_real {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ ≤ Real.Gamma σ := by
  calc
    ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ =
        ‖Complex.Gamma ((σ : ℂ) + ((|T| : ℝ) : ℂ) * I)‖ := (gamma_norm_abs σ T).symm
    _ ≤ ‖Complex.Gamma ((σ : ℂ) + (0 : ℂ) * I)‖ :=
      gamma_norm_antitone hσ (show (0 : ℝ) ∈ Set.Ici 0 from le_refl (0 : ℝ))
        (show |T| ∈ Set.Ici (0 : ℝ) from abs_nonneg T) (abs_nonneg T)
    _ = Real.Gamma σ := by
      simp [Complex.Gamma_ofReal, abs_of_nonneg (Real.Gamma_pos_of_pos hσ).le]

#print axioms gamma_norm_le_real

/-- The recurrence gives a polynomial tail bound of every natural degree. -/
theorem gamma_norm_mul_pow_le_real {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (m : ℕ) :
    |T| ^ m * ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ ≤ Real.Gamma (σ + m) := by
  induction m generalizing σ with
  | zero => simpa using gamma_norm_le_real hσ T
  | succ m ih =>
    have hσ1 : 0 < σ + 1 := by linarith
    have hz : (σ : ℂ) + (T : ℂ) * I ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
    have hnorm : |T| ≤ ‖(σ : ℂ) + (T : ℂ) * I‖ := by
      simpa using Complex.abs_im_le_norm ((σ : ℂ) + (T : ℂ) * I)
    have hrec : ‖Complex.Gamma (((σ + 1 : ℝ) : ℂ) + (T : ℂ) * I)‖ =
        ‖(σ : ℂ) + (T : ℂ) * I‖ * ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ := by
      rw [show ((σ + 1 : ℝ) : ℂ) + (T : ℂ) * I =
        ((σ : ℂ) + (T : ℂ) * I) + 1 by push_cast; ring,
        Complex.Gamma_add_one _ hz, norm_mul]
    calc
      |T| ^ (m + 1) * ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ =
          |T| ^ m * (|T| * ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖) := by ring
      _ ≤ |T| ^ m * ‖Complex.Gamma (((σ + 1 : ℝ) : ℂ) + (T : ℂ) * I)‖ := by
        rw [hrec]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (by positivity)
      _ ≤ Real.Gamma (σ + 1 + m) := ih hσ1
      _ = Real.Gamma (σ + (m + 1 : ℕ)) := by congr 1; push_cast; ring

#print axioms gamma_norm_mul_pow_le_real

/-- A uniform tail bound also covers ordinates close to zero. -/
theorem gamma_norm_mul_one_add_abs_pow_le {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (m : ℕ) :
    (1 + |T|) ^ m * ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ ≤
      2 ^ m * max (Real.Gamma σ) (Real.Gamma (σ + m)) := by
  by_cases hT : |T| ≤ 1
  · have hp : (1 + |T|) ^ m ≤ (2 : ℝ) ^ m :=
      pow_le_pow_left₀ (by positivity) (by linarith) m
    calc
      (1 + |T|) ^ m * ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ ≤
          2 ^ m * Real.Gamma σ :=
        mul_le_mul hp (gamma_norm_le_real hσ T) (norm_nonneg _) (by positivity)
      _ ≤ 2 ^ m * max (Real.Gamma σ) (Real.Gamma (σ + m)) := by gcongr; exact le_max_left _ _
  · have hT1 : 1 ≤ |T| := (lt_of_not_ge hT).le
    have hp : (1 + |T|) ^ m ≤ (2 * |T|) ^ m :=
      pow_le_pow_left₀ (by positivity) (by linarith) m
    calc
      (1 + |T|) ^ m * ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ ≤
          (2 * |T|) ^ m * ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = 2 ^ m * (|T| ^ m * ‖Complex.Gamma ((σ : ℂ) + (T : ℂ) * I)‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ m * Real.Gamma (σ + m) :=
        mul_le_mul_of_nonneg_left (gamma_norm_mul_pow_le_real hσ T m) (by positivity)
      _ ≤ 2 ^ m * max (Real.Gamma σ) (Real.Gamma (σ + m)) := by gcongr; exact le_max_right _ _

#print axioms gamma_norm_mul_one_add_abs_pow_le

end LeanLab.Ternary78.Bennett
