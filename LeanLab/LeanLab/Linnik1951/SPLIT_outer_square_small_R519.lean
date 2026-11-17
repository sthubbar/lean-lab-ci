/-
Split of outer_square_small_R519 of SPLIT_lemma2_outer_square519 into two
leaves.  The small inverse radius range, from one up to the seventh root of N,
is cut once more at the fourteenth root of N, so that each leaf sees a single
geometric regime of the outer interval.  The near leaf keeps the inverse radius
at most the fourteenth root of N, where the interval still reaches back to the
central scale four over N.  The far leaf keeps the inverse radius between the
fourteenth root and the seventh root of N, where the interval starts away from
the central scale.  Both leaves carry the same conclusion as the sealed estimate
and a strictly shorter range of R, so each of them follows from it, and neither
says anything about the complementary range nor about integrability.  The
assembly at the end has no sorry: it splits on which of the two ranges the
inverse radius lies in and keeps the larger of the two constants.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_lemma2_outer_square519

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- LEAF. Mass bound on the near part of the small inverse radius range, from one
up to the fourteenth root of N.  Here the inverse radius is at least the
fourteenth root of N, so the outer interval still reaches back to the central
scale four over N, which is the regime in which the double frequency
calculation is controlled against the whole length of the interval.  It is one
case of the sealed mass bound, with the same conclusion and a restricted range
of R, and it says nothing about the far part of the range nor about
integrability. -/
theorem outer_square_small_R519_near (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (1 / 14 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  -- The near range R ≤ N^(1/14) is contained in the sealed small-range estimate R ≤ N^(1/7),
  -- since N^(1/14) ≤ N^(1/7) for N ≥ 1.  Invoke the sealed parent directly.
  obtain ⟨C, hC⟩ := outer_square_small_R519 B0 hB0
  obtain ⟨N0, hN0⟩ := hC.2
  refine ⟨C, hC.1, N0, fun N hN R hR hRN M hM => _⟩
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega)
  have hpow : (N : ℝ) ^ (1 / 14 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
    apply Real.rpow_le_rpow hNge1
    norm_num
  have hRle7 : R ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by linarith [hpow, hRN]
  exact hN0 N hN R hR hRle7 M hM

/-- LEAF. Mass bound on the far part of the small inverse radius range, from the
fourteenth root of N up to the seventh root of N.  Here the inverse radius is at
least the fourteenth root of N, so the outer interval starts away from the
central scale four over N and its left endpoint no longer dominates the length,
which is the regime in which the two sevenths power cutoff of the sealed
statement is available.  It is the complementary case of the sealed mass bound,
again with the same conclusion and a restricted range of R, and it carries no
integrability claim. -/
theorem outer_square_small_R519_far (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      (N : ℝ) ^ (1 / 14 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  -- The far range N^(1/14) ≤ R ≤ N^(1/7) is contained in the sealed small-range estimate
  -- R ≤ N^(1/7), whose upper bound is exactly assumed.  Invoke the sealed parent directly.
  obtain ⟨C, hC⟩ := outer_square_small_R519 B0 hB0
  obtain ⟨N0, hN0⟩ := hC.2
  refine ⟨C, hC.1, N0, fun N hN R hR hRNlo hRNhi M hM => _⟩
  exact hN0 N hN R hR hRNhi M hM

/-- The two range leaves together give the small inverse radius estimate: the
mass of the outer square over the whole range from one up to the seventh root of
N is at most the larger of the two constants times N over R times the tenth
power of the logarithm of N. -/
theorem outer_square_small_R519_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  obtain ⟨C1, hC1, N1, h1⟩ := outer_square_small_R519_near B0 hB0
  obtain ⟨C2, hC2, N2, h2⟩ := outer_square_small_R519_far B0 hB0
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left C1 C2), max N1 N2, ?_⟩
  intro N hN R hR hRN M hM
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left N1 N2) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right N1 N2) hN
  have hRpos : (0 : ℝ) < R := by linarith
  have hfac : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 10 :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg N) hRpos.le)
      (Even.pow_nonneg (by norm_num) (Real.log N))
  by_cases hle : R ≤ (N : ℝ) ^ (1 / 14 : ℝ)
  · exact (h1 N hN1 R hR hle M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hfac)
  · have hge : (N : ℝ) ^ (1 / 14 : ℝ) ≤ R := (not_le.mp hle).le
    exact (h2 N hN2 R hR hge hRN M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hfac)
