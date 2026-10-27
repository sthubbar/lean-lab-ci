import LeanLab.Pintz2021.VaughanBoundTask08
import LeanLab.Pintz2021.Moment510U1357

/-!
P0054 author copy page 17 display 5.11.
This combines the proved Vaughan bound and the proved fourth moment bound.
The sum covers all positive m at most N and has log power 6.
The major arc inputs remain conditional.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.Minor511Task08

open Finset MinorArcs Holder511 Moment510U1357 Lemma1U1369 VaughanBoundTask08

/-- Display 5.11 without cited minor arc or moment hypotheses. -/
theorem minor511_proved : ∃ A : ℝ, 0 ≤ A ∧
    ∀ (X1 : ℝ) (N : ℕ) (P : ℝ), 4 ≤ N → 2 ≤ X1 → X1 ≤ (N : ℝ) ^ 2 →
      1 ≤ P → P ≤ (N : ℝ) ^ 2 → ((N : ℝ) ^ 2) ^ (2 / 5 : ℝ) ≤ P →
      ∀ mi : Set ℝ, MeasurableSet mi → mi ⊆ (majorArcs P ((N : ℝ) ^ 2 / P))ᶜ →
      ∑ m ∈ Icc 1 N, ‖R2 (S X1 ((N : ℝ) ^ 2)) mi (2 * m ^ 2)‖ ≤
        (2 * A) ^ (1 / 2 : ℝ) * 2 ^ (3 / 4 : ℝ) * (5 : ℝ) ^ (1 / 4 : ℝ) *
          (N : ℝ) ^ 2 * (N : ℝ) ^ (4 / 5 : ℝ) * Real.log ((N : ℝ) ^ 2) ^ 6 := by
  obtain ⟨A, hA, h1⟩ := lemma1On_proved
  refine ⟨A, hA, ?_⟩
  intro X1 N P hN hX1 hX1X hP1 hPX hP mi hmi hsub
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hX3 : (3 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hL := h1 X1 ((N : ℝ) ^ 2) P hX1 hX1X hX3 hP1 hPX mi hsub
  have hW := moment510_of_display510 (display510_proved N hN)
  simpa using minor511_of_lemma1 hA (by norm_num : (0 : ℝ) ≤ 5)
    (by omega : 2 ≤ N) hP mi hmi hL hW

end LeanLab.Pintz2021.Minor511Task08

#print axioms LeanLab.Pintz2021.Minor511Task08.minor511_proved
