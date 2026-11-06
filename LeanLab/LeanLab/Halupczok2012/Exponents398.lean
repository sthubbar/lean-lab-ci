import LeanLab.Halupczok2012.Statements

/-!
Halupczok journal page 345, the elementary sieve parameter checks.
The logarithmic constant and the threshold 0.861 are checked exactly.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Exponents398

/-- Page 345, the printed lower bound for Lambda 3.
An integer power comparison verifies the logarithmic estimate exactly. -/
theorem lambda3_lower : (2771 / 1000 : ℝ) ≤ Λ3 := by
  have hp : (3 : ℝ) ^ (1771 : ℕ) ≤ (7 : ℝ) ^ (1000 : ℕ) := by
    rw [show (1771 : ℕ) = 7 * 253 by decide, show (1000 : ℕ) = 4 * 250 by decide,
      pow_mul, pow_mul]
    norm_num
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (3 : ℝ) ^ (1771 : ℕ)) hp
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have he : Real.log (27 / 7 : ℝ) = 3 * Real.log 3 - Real.log 7 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (27 : ℝ) = 3 ^ (3 : ℕ) by norm_num,
      Real.log_pow]
    norm_num
  calc
    (2771 / 1000 : ℝ) = 1 + 1771 / 1000 := by norm_num
    _ ≤ 1 + Real.log 7 / Real.log 3 := by
      have hh : (1771 / 1000 : ℝ) ≤ Real.log 7 / Real.log 3 :=
        (le_div_iff₀ h3).mpr (by linarith)
      linarith
    _ = Λ3 := by
      unfold Λ3
      rw [he]
      field_simp [h3.ne']
      ring

/-- Page 345, the inequality needed for the P3 conclusion of Corollary 1.2. -/
theorem cor2_sieve_condition {θ : ℝ} (hθ : (861 / 1000 : ℝ) ≤ θ) :
    1 / θ < (1 - 1 / (2 * θ)) * Λ3 := by
  have ht : 0 < θ := by linarith
  have he : (1 - 1 / (2 * θ)) * Λ3 = ((θ - 1 / 2) * Λ3) / θ := by
    field_simp [ht.ne']
  rw [he, div_lt_div_iff_of_pos_right ht]
  have hm := mul_le_mul_of_nonneg_left lambda3_lower (by linarith : 0 ≤ θ - 1 / 2)
  nlinarith

/-- Page 345, a concrete point in the first exponent range of Corollary 1.4. -/
theorem cor4_first_instance : Cor4Range 1 (3 / 4) := by
  apply Or.inl
  norm_num

/-- Page 345, a concrete point with eta below one half in the second range. -/
theorem cor4_second_instance : Cor4Range 1 (49 / 100) := by
  apply Or.inr
  refine ⟨by norm_num, by norm_num, le_rfl, ?_⟩
  have hmin : (1 : ℝ) < min (1 / (49 / 100 : ℝ) - 1) ((3 - 1 / (49 / 100 : ℝ)) * Λ3 / 2) := by
    apply lt_min
    · norm_num
    · have hl := lambda3_lower
      norm_num at *
      linarith
  have hm0 : (0 : ℝ) < min (1 / (49 / 100 : ℝ) - 1) ((3 - 1 / (49 / 100 : ℝ)) * Λ3 / 2) := by
    linarith
  rw [div_lt_iff₀ hm0]
  simpa using hmin

/-- Page 345, both printed Corollary 1.4 ranges satisfy the P3 sieve inequality. -/
theorem cor4_sieve_condition {θ η : ℝ} (h : Cor4Range θ η) :
    0 < θ ∧ 0 < η ∧
      1 < θ * min (1 - 1 / (2 * θ)) (3 / 2 - 1 / (2 * η)) * Λ3 := by
  have hΛ : 0 < Λ3 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2771 / 1000) lambda3_lower
  have hdiv (x : ℝ) : 1 / (2 * x) = (1 / x) / 2 := by ring
  rcases h with h | h
  · obtain ⟨hθ, hθ1, hη, hη1⟩ := h
    have ht : 0 < θ := by linarith
    have hD : 0 < 1 + 1 / θ := by positivity
    have he : 0 < η := lt_trans (inv_pos.mpr hD) hη
    have hprod : 1 < η * (1 + 1 / θ) :=
      (div_lt_iff₀ hD).mp (by simpa only [one_div] using hη)
    have hi : 1 / η < 1 + 1 / θ := (div_lt_iff₀ he).mpr (by nlinarith)
    have ha : 1 - 1 / (2 * θ) ≤ 3 / 2 - 1 / (2 * η) := by
      rw [hdiv θ, hdiv η]
      linarith
    refine ⟨ht, he, ?_⟩
    rw [min_eq_left ha]
    calc
      (1 : ℝ) = (1 / θ) * θ := by field_simp
      _ < ((1 - 1 / (2 * θ)) * Λ3) * θ :=
        mul_lt_mul_of_pos_right (cor2_sieve_condition (by linarith)) ht
      _ = _ := by ring
  · obtain ⟨hηlo, hηhi, hθhi, hθ⟩ := h
    have he : 0 < η := by linarith
    have hi3 : 1 / η < 3 := (div_lt_iff₀ he).mpr (by linarith)
    have hi1 : 1 < 1 / η := (lt_div_iff₀ he).mpr (by linarith)
    have hD1 : 0 < 1 / η - 1 := by linarith
    have hi30 : 0 < 3 - 1 / η := by linarith
    have hD2 : 0 < (3 - 1 / η) * Λ3 / 2 := by positivity
    have hD : 0 < min (1 / η - 1) ((3 - 1 / η) * Λ3 / 2) := lt_min hD1 hD2
    have ht : 0 < θ := lt_trans (div_pos one_pos hD) hθ
    have hp : 1 < θ * min (1 / η - 1) ((3 - 1 / η) * Λ3 / 2) :=
      (div_lt_iff₀ hD).mp hθ
    have h1 : 1 < θ * (1 / η - 1) := hp.trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) ht.le)
    have h2 : 1 < θ * ((3 - 1 / η) * Λ3 / 2) := hp.trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) ht.le)
    have hi : 1 / θ < 1 / η - 1 := (div_lt_iff₀ ht).mpr (by nlinarith)
    have ha : 3 / 2 - 1 / (2 * η) ≤ 1 - 1 / (2 * θ) := by
      rw [hdiv θ, hdiv η]
      linarith
    refine ⟨ht, he, ?_⟩
    rw [min_eq_right ha, hdiv η]
    nlinarith

end LeanLab.Halupczok2012.Exponents398
