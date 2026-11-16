import LeanLab.Linnik1951.SPLIT_lemma2_outer_square519

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- LEAF. Mass estimate on the lower part of the large inverse radius range.  For a positive line bound, sufficiently large N, and inverse radius R between the seventh root of N and the three fourteenths power of N, the squared Mellin transform has outer mass at most C times N over R times the tenth power of the logarithm of N.  This leaf covers only the lower part of the range. -/
theorem outer_square_large_R519_F673_lower (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      (N : ℝ) ^ (1 / 7 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (3 / 14 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  sorry

/-- LEAF. Mass estimate on the upper part of the large inverse radius range.  For a positive line bound, sufficiently large N, and inverse radius R between the three fourteenths power of N and the two sevenths power of N, the squared Mellin transform has outer mass at most C times N over R times the tenth power of the logarithm of N.  This leaf covers only the upper part of the range. -/
theorem outer_square_large_R519_F673_upper (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      (N : ℝ) ^ (3 / 14 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  sorry

/-- The two range estimates combine to give the complete outer square estimate on the large inverse radius range. -/
theorem outer_square_large_R519_F673 (B0 : ℝ) (hB0 : 0 < B0) : ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R → (N : ℝ) ^ (1 / 7 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) → (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤ C * ((N : ℝ) / R * Real.log N ^ 10) := by
  obtain ⟨C1, hC1, N1, h1⟩ := outer_square_large_R519_F673_lower B0 hB0
  obtain ⟨C2, hC2, N2, h2⟩ := outer_square_large_R519_F673_upper B0 hB0
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left C1 C2),
    max N1 N2, ?_⟩
  intro N hN R hR hRlower hRupper M hM
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left N1 N2) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right N1 N2) hN
  have hRnonneg : 0 ≤ (N : ℝ) / R * Real.log N ^ 10 := by
    have hNR : 0 ≤ (N : ℝ) / R := div_nonneg (Nat.cast_nonneg N) (by linarith)
    have hlog : 0 ≤ Real.log N ^ 10 := by
      rw [show Real.log N ^ 10 = (Real.log N ^ 5) ^ 2 by ring]
      exact sq_nonneg _
    exact mul_nonneg hNR hlog
  rcases le_or_gt R ((N : ℝ) ^ (3 / 14 : ℝ)) with hsplit | hsplit
  · exact (h1 N hN1 R hR hRlower hsplit M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hRnonneg)
  · exact (h2 N hN2 R hR hsplit.le hRupper M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hRnonneg)

end LeanLab.Linnik1951.Task519
