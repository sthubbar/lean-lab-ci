import LeanLab.LanguascoPerelli1996.Decomp108

/-!
P0071 pages 354 and 355, the written proof of Lemma 2.
The variation estimate is split at Cauchy Schwarz and partial summation.
All existing declarations keep their statements and proof bodies.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp274a
open Real

/-- LEAF. Page 355, the Cauchy Schwarz display between displays 12 and 13.
Differentiation of the squared norm and Cauchy Schwarz bound variation
by twice the product of the two local L2 norms. The derivative includes
multiplication of each frequency by i, which preserves its norm. -/
theorem band_variation_cauchy_schwarz {X : ℝ} (hX : 0 < X) (U T : ℝ)
    (q : ℕ) [NeZero q] (a : ℕ) :
    (∫ v in (-1 : ℝ)..1, |deriv (Decomp108.energy X U T q a) v|) ≤
      2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) *
        Real.sqrt (∫ v in (-1 : ℝ)..1,
          ‖deriv (fun t : ℝ => zSum (X * Real.exp t) U T q a) v‖ ^ 2) := by
  sorry

/-- LEAF. Page 355, partial summation in the deduction of display 13.
The differentiated band sum has local squared L2 norm bounded by an
absolute constant times T squared times the uniform correlation bound.
This isolates the frequency weighted factor of the Cauchy Schwarz display.
The undifferentiated factor is already bounded by Mass108.band_local_mass. -/
theorem band_derivative_mass :
    GRH → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
        (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
          (∫ v in (-1 : ℝ)..1,
            ‖deriv (fun t : ℝ => zSum (X * Real.exp t) U T q a) v‖ ^ 2) ≤
              C * T ^ 2 * M := by
  sorry

/-- Page 355 display 13, with exactly the statement of variation_control.
CONDITIONAL ON band_variation_cauchy_schwarz and band_derivative_mass. -/
theorem variation_control_decomposed :
    GRH → ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
        (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
          (∫ v in (-1 : ℝ)..1, |deriv (Decomp108.energy X U T q a) v|) ≤ B * T * M := by
  intro hGRH
  obtain ⟨C, hC, hd⟩ := band_derivative_mass hGRH
  refine ⟨4 * Real.exp 2 + C, by positivity, ?_⟩
  intro X hX U T hU hUT hT q inst a ha M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM U le_rfl hUT.le)
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hm : (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) ≤
      (4 * Real.exp 2) * M := by
    have hb := Mass108.band_local_mass hX U T hUT.le q a
    have he := Real.exp_pos (2 : ℝ)
    have hu := hM U le_rfl hUT.le
    have ht := hM T hUT.le le_rfl
    nlinarith
  have hd' := hd X hX U T hU hUT hT q a ha M hM
  have hs : Real.sqrt (C * T ^ 2 * M) = T * Real.sqrt (C * M) := by
    rw [show C * T ^ 2 * M = T ^ 2 * (C * M) by ring,
      Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT0]
  have hy : 2 * Real.sqrt ((4 * Real.exp 2) * M) * Real.sqrt (C * M) ≤
      (4 * Real.exp 2) * M + C * M := by
    nlinarith [sq_nonneg (Real.sqrt ((4 * Real.exp 2) * M) - Real.sqrt (C * M)),
      Real.sq_sqrt (show 0 ≤ (4 * Real.exp 2) * M by positivity),
      Real.sq_sqrt (mul_nonneg hC hM0)]
  calc
    _ ≤ 2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) *
        Real.sqrt (∫ v in (-1 : ℝ)..1,
          ‖deriv (fun t : ℝ => zSum (X * Real.exp t) U T q a) v‖ ^ 2) :=
      band_variation_cauchy_schwarz hX U T q a
    _ ≤ 2 * Real.sqrt ((4 * Real.exp 2) * M) * Real.sqrt (C * T ^ 2 * M) := by
      gcongr
    _ = T * (2 * Real.sqrt ((4 * Real.exp 2) * M) * Real.sqrt (C * M)) := by
      rw [hs]; ring
    _ ≤ T * ((4 * Real.exp 2) * M + C * M) := mul_le_mul_of_nonneg_left hy hT0
    _ = (4 * Real.exp 2 + C) * T * M := by ring


end LeanLab.LanguascoPerelli1996.Decomp274a

#print axioms LeanLab.LanguascoPerelli1996.Decomp274a.band_variation_cauchy_schwarz
#print axioms LeanLab.LanguascoPerelli1996.Decomp274a.band_derivative_mass
#print axioms LeanLab.LanguascoPerelli1996.Decomp274a.variation_control_decomposed
