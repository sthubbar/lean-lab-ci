/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 172 to 175 Theorem 2 and pages 184 to 185 display 7.1 and Corollary 2.
The finite numerical leaf is separate from the uniform analytic transfer.
-/
import LeanLab.PlattTrudgian2014.Decomp281a
import LeanLab.PlattTrudgian2014.Decomp125b

namespace LeanLab.PlattTrudgian2014

open MeasureTheory

/-- P0026 page 174, the normalized dyadic sum E star at length M. -/
noncomputable def dyadicMoment281 (t : ℝ) (M : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(M : ℤ)) *
    ∑ k ∈ Finset.range (2 ^ M), Real.exp (t * (G M ((k : ℝ) / (2 : ℝ) ^ M)).re)

/-- LEAF. P0026 pages 174 to 175, Theorem 2 part b, displays 4.5 to 4.12.
A single finite dyadic sum bounds the exponential rate of every real moment.
This leaf has no norm comparison and no numerical large values threshold. -/
theorem dyadic_real_moment_bound281 (t : ℝ) (M : ℕ) (ht : 0 ≤ t) (hM : 0 < M)
    (L : ℕ) :
    (∫ x : ℝ in 0..1, Real.exp (t * (G L x).re)) ≤
      Real.exp ((Real.log (dyadicMoment281 t M) / M) * L) := by
  sorry

/-- LEAF. P0026 pages 184 to 185, display 7.1 and the Corollary 2 calculation.
Some positive parameter and finite dyadic length give a strict three fifths pressure gap.
The degree 19 polynomial and repeated squaring give this finite numerical input.
This states only the finite calculation and contains no uniform norm moment bound. -/
theorem three_fifths_dyadic_pressure281 :
    ∃ t : ℝ, ∃ M : ℕ, 0 < t ∧ 0 < M ∧
      Real.log (dyadicMoment281 t M) / M + (3 / 5 : ℝ) * Real.log 2 <
        t * 0.7894008449792309 := by
  sorry

/-- P0026 display 7.1 and Corollary 2, exactly the existing moment certificate.
CONDITIONAL ON the finite numerical leaf and the shared analytic comparison leaves. -/
theorem pr_three_fifths_moment_certificate_decomposed281 :
    ∃ t A b : ℝ, 0 < t ∧ 0 ≤ A ∧
      b < t * 0.7894008449792309 - (3 / 5) * Real.log 2 ∧
      ∀ L : ℕ, (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤
        A * Real.exp (b * L) := by
  obtain ⟨t, M, ht, hM, hgap⟩ := three_fifths_dyadic_pressure281
  let p := Real.log (dyadicMoment281 t M) / M
  let δ := (t * 0.7894008449792309 - (3 / 5 : ℝ) * Real.log 2 - p) / 2
  have hδ : 0 < δ := by dsimp [δ, p]; linarith
  obtain ⟨C, hC, hcomp⟩ := norm_real_moment_comparison281 t ht.le
  obtain ⟨B, hB, habs⟩ := sqrt_prefactor_absorbed281 t δ ht.le hδ
  refine ⟨t, C * B, p + δ, ht, mul_nonneg hC hB, ?_, fun L => ?_⟩
  · dsimp [δ, p]
    linarith
  · have hm : (∫ x : ℝ in 0..1, Real.exp (t * (G L x).re)) ≤ Real.exp (p * L) :=
      dyadic_real_moment_bound281 t M ht.le hM L
    calc
      _ ≤ C * (1 + Real.sqrt (t * L)) * Real.exp (p * L) :=
        (hcomp L).trans (mul_le_mul_of_nonneg_left hm (by positivity))
      _ ≤ C * (B * Real.exp (δ * L)) * Real.exp (p * L) := by
        gcongr
        exact habs L
      _ = C * B * (Real.exp (δ * L) * Real.exp (p * L)) := by ring
      _ = C * B * Real.exp ((p + δ) * L) := by
        rw [← Real.exp_add]
        congr 2
        ring

set_option format.width 240

#print axioms dyadic_real_moment_bound281
#print axioms three_fifths_dyadic_pressure281
#print axioms pr_three_fifths_moment_certificate_decomposed281

end LeanLab.PlattTrudgian2014
