import LeanLab.BHP1997.DecompC165a

namespace LeanLab.BHP1997.DecompC165a
open Classical Complex MeanValue132

/-- LEAF. The conductor and height step shows that the base of the power
is at least one. This is the lower bound used when comparing the analytic
estimate with the requested sum. -/
theorem conductor_height_base_F172 {q : ℕ} [NeZero q] (hq : 1 ≤ q) (t : ℝ) :
    1 ≤ (q : ℝ) * (|t| + 1) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  nlinarith [abs_nonneg t]

/-- LEAF. The pole-distance step shows that the distance from the point
to one is strictly positive when the point is not one. This makes the
reciprocal pole term nonnegative. -/
theorem pole_distance_positive_F172 {σ t : ℝ}
    (hne : (σ : ℂ) + t * Complex.I ≠ 1) :
    0 < ‖(σ : ℂ) + t * Complex.I - 1‖ := by
  rw [norm_pos_iff]
  intro hzero
  apply hne
  have hshift := congrArg (fun z : ℂ => z + 1) hzero
  simpa using hshift

/-- LEAF. The right half of the analytic convexity step gives one
uniform constant for a maximum estimate. The maximum contains the
conductor height power and the reciprocal distance to the pole. -/
theorem convexity_max_right_F172 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
        (σ : ℂ) + t * Complex.I ≠ 1 →
        ‖χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤
          C * max (((q : ℝ) * (|t| + 1)) ^ ((1 - σ) / 2 + ε))
            (1 / ‖(σ : ℂ) + t * Complex.I - 1‖) := by
  sorry

/-- LEAF. The left half of the analytic convexity step gives one
uniform constant for the same maximum estimate. This supplies the
remaining part of the closed strip. -/
theorem convexity_max_left_F172 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ t : ℝ, 0 ≤ σ → σ < 1 / 2 →
        (σ : ℂ) + t * Complex.I ≠ 1 →
        ‖χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤
          C * max (((q : ℝ) * (|t| + 1)) ^ ((1 - σ) / 2 + ε))
            (1 / ‖(σ : ℂ) + t * Complex.I - 1‖) := by
  sorry

/-- LEAF. The summation step bounds the maximum of two nonnegative
terms by their sum. This converts each maximum estimate into the form
required by the final estimate. -/
theorem max_le_sum_F172 {A d : ℝ} (hA : 0 ≤ A) (hd : 0 < d) :
    max A (1 / d) ≤ A + 1 / d := by
  apply max_le
  · linarith [one_div_pos.mpr hd]
  · linarith [hA]

/-- The final summation step applies the maximum estimate on the part
of the strip selected by sigma and then uses the sum comparison. It
also records that the analytic constant is positive. -/
theorem rademacher_convexity_F172 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 →
        (σ : ℂ) + t * Complex.I ≠ 1 →
        ‖χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤
          C * (((q : ℝ) * (|t| + 1)) ^ ((1 - σ) / 2 + ε) +
            1 / ‖(σ : ℂ) + t * Complex.I - 1‖) := by
  intro ε hε
  by_cases hσ : 1 / 2 ≤ σ
  · obtain ⟨C, hC, hbound⟩ := convexity_max_right_F172 ε hε
    refine ⟨C, hC, ?_⟩
    intro q _ hq χ σ t _ hσ1 hne
    have hA := conductor_height_base_F172 hq t
    have hd := pole_distance_positive_F172 hne
    have hm := hbound q hq χ σ t hσ hσ1 hne
    have hs := max_le_sum_F172 hA.le hd
    exact hm.trans (mul_le_mul_of_nonneg_left hs hC.le)
  · obtain ⟨C, hC, hbound⟩ := convexity_max_left_F172 ε hε
    refine ⟨C, hC, ?_⟩
    intro q _ hq χ σ t hσ0 _ hne
    have hA := conductor_height_base_F172 hq t
    have hd := pole_distance_positive_F172 hne
    have hlt : σ < 1 / 2 := lt_of_not_ge hσ
    have hm := hbound q hq χ σ t hσ0 hlt hne
    have hs := max_le_sum_F172 hA.le hd
    exact hm.trans (mul_le_mul_of_nonneg_left hs hC.le)

end LeanLab.BHP1997.DecompC165a
