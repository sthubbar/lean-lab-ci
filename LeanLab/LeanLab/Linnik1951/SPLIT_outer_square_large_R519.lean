/-
Split of outer_square_large_R519 of SPLIT_lemma2_outer_square519 into two leaves.
The large inverse radius range of the outer square estimate, from the seventh
root of N up to the two sevenths power of N, is cut at the one half of that
range, the three fourteenths power of N.  Each leaf carries the same mass
estimate on one of the two halves of the radius range, and is therefore
strictly easier than the sealed estimate: one range of the radius is replaced
by a shorter one, the conclusion and the constant shape are unchanged.  The
assembly at the end has no sorry, splits on which half the inverse radius lies
in and keeps the sum of the two constants; it does not use the sealed theorem
itself.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_lemma2_outer_square519

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- LEAF. Mass bound on the lower half of the large inverse radius range, from the
seventh root of N up to the three fourteenths power of N.  This is the part of
the sealed estimate in which the outer interval from four over N to one over R
is still long: the radius is at most the three fourteenths power of N, so the
interval reaches at least that far out from the central scale four over N.  The
conclusion is the sealed mass bound with the same constant shape, and the radius
is restricted to the lower half of its range, so the statement is strictly
weaker than the sealed one. -/
theorem outer_square_large_R_lower_band519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      (N : ℝ) ^ (1 / 7 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (3 / 14 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  sorry

/-- LEAF. Mass bound on the upper half of the large inverse radius range, from the
three fourteenths power of N up to the two sevenths power of N.  This is the part
of the sealed estimate in which the outer interval from four over N to one over R
is short: the radius is at least the three fourteenths power of N, so the
interval stops early and the mass factor N over R is small.  The conclusion is
the sealed mass bound with the same constant shape, and the radius is restricted
to the upper half of its range, so the statement is strictly weaker than the
sealed one. -/
theorem outer_square_large_R_upper_band519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      (N : ℝ) ^ (3 / 14 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  sorry

/-- The two band leaves together give the sealed large inverse radius estimate:
the square of the Mellin transform has mass at most the sum of the two band
constants times N over R times the tenth power of the logarithm of N. -/
theorem outer_square_large_R519_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      (N : ℝ) ^ (1 / 7 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  obtain ⟨C1, hC1, N1, h1⟩ := outer_square_large_R_lower_band519 B0 hB0
  obtain ⟨C2, hC2, N2, h2⟩ := outer_square_large_R_upper_band519 B0 hB0
  refine ⟨C1 + C2, by linarith, max N1 N2, ?_⟩
  intro N hN R hR hRlo hRhi M hM
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left N1 N2) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right N1 N2) hN
  have hX : 0 ≤ (N : ℝ) / R * Real.log N ^ 10 := by
    have hRp : (0 : ℝ) < R := by linarith
    have hNR : (0 : ℝ) ≤ (N : ℝ) / R := div_nonneg (Nat.cast_nonneg N) hRp.le
    have hlog : (0 : ℝ) ≤ Real.log N ^ 10 := by
      have he : Real.log N ^ 10 = (Real.log N ^ 5) ^ 2 := by ring
      rw [he]
      exact sq_nonneg _
    exact mul_nonneg hNR hlog
  by_cases hs : R ≤ (N : ℝ) ^ (3 / 14 : ℝ)
  · exact (h1 N hN1 R hR hRlo hs M hM).trans
      (mul_le_mul_of_nonneg_right (by linarith : C1 ≤ C1 + C2) hX)
  · have hl : (N : ℝ) ^ (3 / 14 : ℝ) ≤ R := le_of_lt (not_le.mp hs)
    exact (h2 N hN2 R hR hl hRhi M hM).trans
      (mul_le_mul_of_nonneg_right (by linarith : C2 ≤ C1 + C2) hX)

end LeanLab.Linnik1951.Task519
