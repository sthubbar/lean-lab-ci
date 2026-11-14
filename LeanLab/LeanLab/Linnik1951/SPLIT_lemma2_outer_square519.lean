/-
Split of lemma2_outer_square519 of Decomp519a into three leaves.  The signed
outer square estimate of Lemma 2 is cut in two ways.  One leaf carries the
measure theoretic half alone, that the square of the Mellin transform is
integrable on the outer interval; it asks for no constant and no size.  The
other two carry the mass bound itself, one on the range of the inverse radius
below the seventh root of N and one on the range above it.  The assembly at the
end has no sorry, splits on which range the inverse radius lies in and keeps the
larger of the two constants; it does not use the split theorem itself.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp519a

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- LEAF. Integrability half of the outer interval.  For a positive line constant
B0, once N is large enough, and for every inverse radius R between one and the
two sevenths power of N, every continuous coefficient obeying the cubic
logarithmic line bound has square norm integrable over the outer interval from
four over N to one over R.  This is the first conjunct alone: it carries no
constant, no factor of N over R and no power of the logarithm, so it is strictly
weaker than the sealed estimate. -/
theorem outer_square_integrable519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
            (Set.Icc (4 / (N : ℝ)) (1 / R)) := by
  sorry

/-- LEAF. Mass bound on the small inverse radius range, from one up to the seventh
root of N.  Here the outer interval is at least as long as the central one, so
this is the case of the estimate in which the inverse radius is short and the
interval reaches back to the central scale four over N.  It is one case of the
sealed mass bound, with the same conclusion and a restricted range of R, and it
says nothing about the complementary range nor about integrability. -/
theorem outer_square_small_R519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  sorry

/-- LEAF. Mass bound on the large inverse radius range, from the seventh root of N
up to the two sevenths power of N.  Here the outer interval lies far from the
central scale, which is the case in which the double frequency calculation is
cut off only by the two sevenths power of N in the statement of Lemma 2.  It is
the complementary case of the sealed mass bound, again with the same conclusion
and a restricted range of R, and it carries no integrability claim. -/
theorem outer_square_large_R519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      (N : ℝ) ^ (1 / 7 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  sorry

/-- The three leaves together give the outer square estimate: the square of the
Mellin transform is integrable on the outer interval, and its mass there is at
most the larger of the two range constants times N over R times the tenth power
of the logarithm of N. -/
theorem lemma2_outer_square519_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
            (Set.Icc (4 / (N : ℝ)) (1 / R)) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  obtain ⟨Ni, hi⟩ := outer_square_integrable519 B0 hB0
  obtain ⟨C1, hC1, N1, h1⟩ := outer_square_small_R519 B0 hB0
  obtain ⟨C2, hC2, N2, h2⟩ := outer_square_large_R519 B0 hB0
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left C1 C2),
    max Ni (max N1 N2), ?_⟩
  intro N hN R hR hRN M hM
  have hNi : Ni < N := lt_of_le_of_lt (le_max_left Ni (max N1 N2)) hN
  have hN1 : N1 < N :=
    lt_of_le_of_lt ((le_max_left N1 N2).trans (le_max_right Ni (max N1 N2))) hN
  have hN2 : N2 < N :=
    lt_of_le_of_lt ((le_max_right N1 N2).trans (le_max_right Ni (max N1 N2))) hN
  refine ⟨hi N hNi R hR hRN M hM, ?_⟩
  have hRp : (0 : ℝ) < R := by linarith
  have hX : 0 ≤ (N : ℝ) / R * Real.log N ^ 10 := by
    have hNR : (0 : ℝ) ≤ (N : ℝ) / R := div_nonneg (Nat.cast_nonneg N) hRp.le
    have hlog : (0 : ℝ) ≤ Real.log N ^ 10 := by
      have he : Real.log N ^ 10 = (Real.log N ^ 5) ^ 2 := by ring
      rw [he]
      exact sq_nonneg _
    exact mul_nonneg hNR hlog
  rcases le_or_gt R ((N : ℝ) ^ (1 / 7 : ℝ)) with hs | hl
  · exact (h1 N hN1 R hR hs M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hX)
  · exact (h2 N hN2 R hR hl.le hRN M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hX)

end LeanLab.Linnik1951.Task519
