/-
P0070 Section 6, page 368, equation 41 and its Siegel zero qualification.
These are open Props. No assembly theorem assumes them here.
QUESTION: page 368 prints an upper gap bound, while page 372 uses a lower gap bound.
The two directions are kept separate. No paper error is claimed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Section6

namespace LeanLab.PerelliPintz1992.Section6
open Real

/-- At most one optional real exception for each character and positive modulus. -/
abbrev ExceptionalZeroAssignment :=
  (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → Option ℝ

/-- The nontrivial zero strip form of the zero free assertion in 41. -/
def NontrivialZeroFree41 (exceptional : ExceptionalZeroAssignment) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ)) (β : ℝ),
      exceptional q χ = some β → 0 < β ∧ β < 1 ∧ χ.LFunction (β : ℂ) = 0) ∧
    (∀ (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ)) (ρ : ℂ),
      0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 →
      1 - c / max (log (q : ℝ)) (log (|ρ.im| + 2) ^ (4 / 5 : ℝ)) < ρ.re →
      ∃ β : ℝ, exceptional q χ = some β ∧ ρ = (β : ℂ))

/-- The upper gap direction literally printed below 41 on page 368. QUESTION. -/
def PrintedSiegelUpperGap41 (exceptional : ExceptionalZeroAssignment) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ)) (β : ℝ),
      exceptional q χ = some β → 1 - β ≤ C * (q : ℝ) ^ (-η)

/-- The lower gap direction needed in the first display on page 372. Not the printed direction. -/
def SiegelLowerGapNeeded41 (exceptional : ExceptionalZeroAssignment) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ k : ℝ, 0 < k ∧
    ∀ (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ)) (β : ℝ),
      exceptional q χ = some β → k * (q : ℝ) ^ (-η) ≤ 1 - β

#print axioms NontrivialZeroFree41
#print axioms PrintedSiegelUpperGap41
#print axioms SiegelLowerGapNeeded41

/-- A positive scalar gap can satisfy an upper bound while violating any proposed lower bound. -/
theorem upper_bound_allows_smaller_gap {C k q η : ℝ} (hC : 0 < C) (hk : 0 < k) (hq : 0 < q) :
    ∃ d : ℝ, 0 < d ∧ d ≤ C * q ^ (-η) ∧ d < k * q ^ (-η) := by
  have hm : 0 < min C k := lt_min hC hk
  have hp : 0 < q ^ (-η) := Real.rpow_pos_of_pos hq _
  have hl : min C k / 2 ≤ C := by linarith [min_le_left C k]
  have hr : min C k / 2 < k := by linarith [min_le_right C k]
  exact ⟨min C k / 2 * q ^ (-η), mul_pos (div_pos hm (by norm_num)) hp,
    mul_le_mul_of_nonneg_right hl hp.le, mul_lt_mul_of_pos_right hr hp⟩

#print axioms upper_bound_allows_smaller_gap

end LeanLab.PerelliPintz1992.Section6
