/-
Baker, Harman and Pintz 1997, unit U-1609, audit of the statement repairs in DecompC165c and
DecompC165d. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165d
import LeanLab.BHP1997.InstancesC165

namespace LeanLab.BHP1997.Audit1609
open MeanSquareC165 DecompC165b DecompC165d

/-- Display 3.4 with `0 ≤ V` in place of `0 < V` is false: in Lean `E / 0 ^ 2 = 0`, so at `V = 0` the
right side vanishes on a nonempty set. The tree's `Lemma1LargeValues` carries `0 < V`. -/
theorem large_values_zero_V_false :
    ¬ (∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ C : ℝ, 0 < C ∧
      ∀ x F T V : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
        2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
        0 ≤ V → Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
          (S.card : ℝ) ≤ C * Real.log x ^ 2 *
            (energy a c1 c2 F * F / V ^ 2 +
              energy a c1 c2 F ^ 3 * F * (q : ℝ) * T / V ^ 6)) := by
  intro h
  obtain ⟨C, -, hC⟩ := h 0 1 2 (by norm_num) (by norm_num)
  have hb := hC 16 2 3 0 1 {(0, (1 : DirichletCharacter ℂ 1))} (fun _ => 0)
    (fun n => by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    le_rfl (by norm_num) le_rfl
    (by
      intro p hp p' hp' hne _
      simp only [Finset.mem_singleton] at hp hp'
      exact absurd (hp.trans hp'.symm) hne)
    (by intro p hp; simp only [Finset.mem_singleton] at hp; subst hp; norm_num)
    (fun p _ => norm_nonneg _)
  norm_num at hb

/-- The hypotheses of `EnergyLogBound` hold for a nonzero sequence with a nonempty energy sum. -/
theorem energy_log_bound_instance :
    Thm4.CoeffBound (fun n => if n = 0 then 0 else 1) 0 ∧ (2 : ℝ) ≤ 2 ∧ (0 : ℝ) < 1 / 2 ∧
      (1 / 2 : ℝ) < 3 := by
  refine ⟨fun n => ?_, by norm_num, by norm_num, by norm_num⟩
  by_cases hn : n = 0 <;> simp [hn]

/-- `right_density_mono` has its hypotheses at the zero weight, with `v0 = v1 = 0`. -/
theorem right_density_mono_instance (ε : ℝ) (hε : 0 < ε) :
    (0 : ℝ) ≤ 0 :=
  DecompC165d.right_density_mono hε (InstancesC165.right_conditions_zero ε) (InstancesC165.right_conditions_zero ε)
    ⟨0, fun _ _ _ _ => le_rfl⟩

/-- `E₂` is not empty: the point `(3/10, 3/10)` lies in it for every admissible `ε`. -/
theorem lowerTwoDiscarded_nonempty {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10 ^ 8) :
    lowerTwoDiscarded ε (3 / 10) (3 / 10) := by
  unfold lowerTwoDiscarded upperPairRegion
  refine ⟨by norm_num; linarith, le_rfl, by norm_num, by norm_num, ?_⟩
  rintro (h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, h, -⟩)
  all_goals norm_num at h
  all_goals linarith

#print axioms large_values_zero_V_false
#print axioms energy_log_bound_instance
#print axioms right_density_mono_instance
#print axioms lowerTwoDiscarded_nonempty
#print axioms LeanLab.BHP1997.DecompC165c.section3_mean_values
#print axioms LeanLab.BHP1997.DecompC165d.section5_weights
#print axioms LeanLab.BHP1997.DecompC165d.lower_short_weight

end LeanLab.BHP1997.Audit1609
