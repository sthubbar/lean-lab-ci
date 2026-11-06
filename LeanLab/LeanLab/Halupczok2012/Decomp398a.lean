import LeanLab.Halupczok2012.Max398
import LeanLab.Halupczok2012.Fourier398

/-!
Supply decomposition for the maximum supplement of Halupczok Theorem 7.
Source: Halupczok journal page 343, display 4.1 and its last paragraph.
The analytic input is reduced through U1496PP to Perelli Pintz 1993.
The latter proof is on pages 43 to 46, displays 1, 4 and 5.
https://doi.org/10.1112/jlms/s2-47.1.41
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp398a

open Finset MeasureTheory
open scoped Classical ArithmeticFunction.vonMangoldt

/-- LEAF. Perelli Pintz pages 43 to 44, display 1, Fourier extraction before squaring.
The two integrals use complementary measurable arc sets in a unit interval.
This finite identity contains no prime distribution estimate. -/
theorem fourier_partition (ε A N Y : ℝ) (hN : 1 ≤ N) (hY : 0 ≤ Y) (hYN : Y ≤ N) (m : ℕ) :
    (ppR m N Y : ℂ) = arcCoeff N Y m (majorArcs N Y ε A) +
      arcCoeff N Y m (arcBase Y ε \ majorArcs N Y ε A) :=
  Fourier398.partition ε A N Y hYN m

/-- LEAF. Perelli Pintz page 44 display 4, proved in section 4 on pages 45 to 46.
Only the major arc coefficient is compared with the singular series main term. -/
theorem major_energy :
    ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ,
      N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
      ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        ‖arcCoeff N Y (2 * k) (majorArcs N Y ε A) -
          ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ^ 2 ≤
        C * Y ^ (1 / 3 + ε) * Y ^ 2 * Real.log N ^ (-A) := by
  sorry

/-- LEAF. Perelli Pintz page 44 displays 3 and 5 and section 5 on pages 46 to 49.
This is the minor arc mean square obtained from the local S2 integral bound.
It has no singular series main term. -/
theorem minor_energy :
    ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ,
      N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
      ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        ‖arcCoeff N Y (2 * k) (arcBase Y ε \ majorArcs N Y ε A)‖ ^ 2 ≤
        C * Y ^ (1 / 3 + ε) * Y ^ 2 * Real.log N ^ (-A) := by
  sorry

/-- Perelli Pintz page 44 display 1, the two arc energies imply the existing Goldbach input. -/
theorem pp1993_goldbach : PP1993Goldbach := by
  intro ε A hε hA
  obtain ⟨CM, NM, hM⟩ := major_energy ε A hε hA
  obtain ⟨Cm, Nm, hm⟩ := minor_energy ε A hε hA
  refine ⟨2 * (CM + Cm), max 1 (max NM Nm), ?_⟩
  intro N Y hN hlow hYN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hY0 : 0 ≤ Y := (Real.rpow_nonneg (by linarith : 0 ≤ N) _).trans hlow
  have hM' := hM N Y ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) hlow hYN
  have hm' := hm N Y ((le_max_right _ _).trans ((le_max_right _ _).trans hN)) hlow hYN
  have hsplit : ∀ k : ℕ,
      (ppR (2 * k) N Y - S (2 * k) * ppM (2 * k) N Y) ^ 2 ≤
        2 * (‖arcCoeff N Y (2 * k) (majorArcs N Y ε A) -
          ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ^ 2 +
          ‖arcCoeff N Y (2 * k) (arcBase Y ε \ majorArcs N Y ε A)‖ ^ 2) := by
    intro k
    let u := arcCoeff N Y (2 * k) (majorArcs N Y ε A) -
      ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)
    let v := arcCoeff N Y (2 * k) (arcBase Y ε \ majorArcs N Y ε A)
    have he : ((ppR (2 * k) N Y - S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ) = u + v := by
      push_cast
      rw [fourier_partition ε A N Y hN1 hY0 hYN]
      dsimp [u, v]
      push_cast
      ring
    have hn := norm_add_le u v
    have hsq := pow_le_pow_left₀ (norm_nonneg (u + v)) hn 2
    have hr : ‖((ppR (2 * k) N Y - S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ^ 2 =
        (ppR (2 * k) N Y - S (2 * k) * ppM (2 * k) N Y) ^ 2 := by
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [he] at hr
    dsimp [u, v] at *
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  calc
    _ ≤ ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        2 * (‖arcCoeff N Y (2 * k) (majorArcs N Y ε A) -
          ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ^ 2 +
          ‖arcCoeff N Y (2 * k) (arcBase Y ε \ majorArcs N Y ε A)‖ ^ 2) :=
      sum_le_sum fun k _ => hsplit k
    _ = 2 * ((∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        ‖arcCoeff N Y (2 * k) (majorArcs N Y ε A) -
          ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ^ 2) +
        ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
          ‖arcCoeff N Y (2 * k) (arcBase Y ε \ majorArcs N Y ε A)‖ ^ 2) := by
      rw [← mul_sum, sum_add_distrib]
    _ ≤ _ := by linarith

/-- Exact statement of the sealed theorem_7_max, assembled from the three smaller leaves. -/
theorem theorem7_max : Theorem7Max :=
  Max398.theorem7Max_of_PP1993 pp1993_goldbach

end LeanLab.Halupczok2012.Decomp398a
