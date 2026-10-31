import LeanLab.ChirreHagen2025.Statements

/-!
Decomposition of P0075 Lemma 2.4, pages 5 and 6.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp122

/-- LEAF. P0075 page 5, equation 2.11 and the next display.
The Laurent remainder bound uses the Stieltjes coefficient estimate from reference 2. -/
theorem zeta_remainder (t : ℝ) (ht : 0 < t) (htop : t ≤ 1 / 2) :
    ‖riemannZeta (1 + t * Complex.I) - 1 / (t * Complex.I)‖ ≤ 0.951 := by
  sorry

/-- LEAF. P0075 page 6, first display, obtained by differentiating equation 2.11.
The coefficient estimate is from reference 2, cited on page 5. -/
theorem deriv_remainder (t : ℝ) (ht : 0 < t) (htop : t ≤ 1 / 2) :
    ‖deriv riemannZeta (1 + t * Complex.I) - 1 / (t : ℂ) ^ 2‖ ≤ 0.862 := by
  sorry

/-- LEAF. P0075 page 6, the final quotient estimate in the proof of Lemma 2.4. -/
theorem quotient_bound (t : ℝ) (ht : 0 < t) (htop : t ≤ 1 / 2)
    (z d : ℂ) (hz : ‖z - 1 / (t * Complex.I)‖ ≤ 0.951)
    (hd : ‖d - 1 / (t : ℂ) ^ 2‖ ≤ 0.862) :
    ‖d / z + 1 / (t * Complex.I)‖ ≤ 2.635 := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have hw0 : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero ht0 Complex.I_ne_zero
  have hw : ‖(t : ℂ) * Complex.I‖ = t := by
    simp [abs_of_pos ht]
  have he : (t : ℂ) * Complex.I * z - 1 =
      (t : ℂ) * Complex.I * (z - 1 / (t * Complex.I)) := by
    field_simp
    <;> ring
  have hden : 1 - 0.951 * t ≤ ‖(t : ℂ) * Complex.I * z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * Complex.I * z)
    have he' : ‖1 - (t : ℂ) * Complex.I * z‖ ≤ t * 0.951 := by
      rw [norm_sub_rev, he, norm_mul, hw]
      exact mul_le_mul_of_nonneg_left hz (le_of_lt ht)
    simp only [norm_one] at h
    linarith
  have hpos : 0 < ‖(t : ℂ) * Complex.I * z‖ := by
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hpos
  have hnumid : (t : ℂ) * Complex.I * d + z =
      (t : ℂ) * Complex.I * (d - 1 / (t : ℂ) ^ 2) +
        (z - 1 / (t * Complex.I)) := by
    field_simp
    ring_nf
    simp [Complex.I_sq]
    <;> ring
  have hnum : ‖(t : ℂ) * Complex.I * d + z‖ ≤ t * 0.862 + 0.951 := by
    rw [hnumid]
    calc
      _ ≤ ‖(t : ℂ) * Complex.I * (d - 1 / (t : ℂ) ^ 2)‖ +
          ‖z - 1 / (t * Complex.I)‖ := norm_add_le _ _
      _ ≤ t * 0.862 + 0.951 := by
        rw [norm_mul, hw]
        exact add_le_add (mul_le_mul_of_nonneg_left hd (le_of_lt ht)) hz
  have hid : d / z + 1 / (t * Complex.I) =
      ((t : ℂ) * Complex.I * d + z) / ((t : ℂ) * Complex.I * z) := by
    field_simp
  rw [hid, norm_div]
  apply (div_le_iff₀ hpos).2
  nlinarith


/-- P0075 Lemma 2.4, assembled with exactly the lab's cited Prop as conclusion.
CONDITIONAL ON the Laurent leaves until their cited input is formalized. -/
theorem lemma2_4_assembled : lemma2_4 := by
  intro t ht htop
  exact quotient_bound t ht htop _ _ (zeta_remainder t ht htop)
    (deriv_remainder t ht htop)

end LeanLab.ChirreHagen2025.Decomp122
