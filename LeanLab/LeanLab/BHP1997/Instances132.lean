/-
P0069, pages 1, 2, 22 and 23. Concrete nonempty consistency instances
for the new decompositions. These are local checks, not proofs of the
uniform analytic inputs. Mathlib singleton sums and Nat.prime_two are
used directly. AI wrote the Lean code. CODEX task132, 2026-10-26.
-/
import LeanLab.BHP1997.Decomp132
import LeanLab.BHP1997.MeanValue132

namespace LeanLab.BHP1997.Instances132
open Classical Complex

/-- Pages 1 and 2, a nonempty prime convolution and admissible densities.
This verifies the local instance recorded for sieve_data. -/
theorem sieve_nonempty_instance :
    (0 : ℝ) < 0.00001 ∧ (0.00001 : ℝ) < 8.8 / 10 ^ 5 ∧
    (0.99 : ℝ) < 1 ∧ (1 : ℝ) < 1.01 ∧ (0.05 : ℝ) < 0.06 ∧ (0.06 : ℝ) < 2.2 ∧
    Decomp132.convolution {2} {2} Decomp132.primeWeight Decomp132.primeWeight 4 = 1 ∧
    |(1 : ℝ) - 1 * 0.06 * (50 / 3)| = 0 := by
  norm_num [Decomp132.convolution, Decomp132.primeWeight]

/-- Pages 11 and 22, a nonempty well-spaced character set in the ranges
x equal to 8, N equal to 2, T equal to 2 and q equal to 1. -/
theorem mean_value_nonempty_instance :
    ∃ S : Finset (ℝ × DirichletCharacter ℂ 1), S.Nonempty ∧
      Thm4.WellSpaced S ∧ (∀ p ∈ S, |p.1| ≤ (2 : ℝ)) := by
  refine ⟨{(0, 1)}, by simp, ?_, ?_⟩
  · simp [Thm4.WellSpaced]
  · simp

/-- Pages 22 and 23, the analytic leaf has a nonempty local witness.
The constant chosen here depends on this sample. No uniform bound follows. -/
theorem perron_nonempty_instance :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℝ × DirichletCharacter ℂ 1 → ℂ,
      (∑ p ∈ ({(0, 1)} : Finset (ℝ × DirichletCharacter ℂ 1)), ‖J p‖ ^ 4) ≤ C * 2 ∧
      ∀ p ∈ ({(0, 1)} : Finset (ℝ × DirichletCharacter ℂ 1)),
        ‖MeanValue132.partialSum 2 p.2 p.1‖ ≤ ‖J p‖ +
          C * Real.log 8 * (Real.sqrt 1 / Real.sqrt 2) +
          C * Real.log 8 * (Real.sqrt 2 / 2) +
          C * (if p.2 = 1 then Real.sqrt 2 / (1 + |p.1|) else 0) := by
  let J : ℝ × DirichletCharacter ℂ 1 → ℂ := fun p => MeanValue132.partialSum 2 p.2 p.1
  let C : ℝ := 1 + ‖MeanValue132.partialSum 2 (1 : DirichletCharacter ℂ 1) 0‖ ^ 4
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, J, ?_, ?_⟩
  · simp only [Finset.sum_singleton]
    dsimp [J, C]
    nlinarith [pow_nonneg (norm_nonneg (MeanValue132.partialSum 2 (1 : DirichletCharacter ℂ 1) 0)) 4]
  · intro p hp
    have hlog : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have h1 : 0 ≤ C * Real.log 8 * (Real.sqrt 1 / Real.sqrt 2) := by positivity
    have h2 : 0 ≤ C * Real.log 8 * (Real.sqrt 2 / 2) := by positivity
    have h3 : 0 ≤ C * (if p.2 = 1 then Real.sqrt 2 / (1 + |p.1|) else 0) := by
      split_ifs <;> positivity
    dsimp only [J]
    linarith

end LeanLab.BHP1997.Instances132
