import LeanLab.Ricci1937.Decomp338b

/-!
Ricci 1937, common greedy cutoff definitions.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary greedy prime endpoint for second memoir pages 109 to 111.
Choose the least endpoint above Y whose remaining block mass is at most its printed target.
The fallback is w when the bounded search is empty. -/
def decomp338GreedyStep (h Y w i : ℕ) : ℕ :=
  if H : ∃ y : ℕ, Y ≤ y ∧ y ≤ w ∧
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ (decomp305HeadMass i : ℝ) / 100
    then Nat.find H else w

/-- Auxiliary decreasing prime cutoffs for second memoir pages 109 to 111.
Apply the greedy endpoint successively at the printed lower block masses. -/
def decomp338GreedyCutoff (h Y t : ℕ) : ℕ → ℕ
  | 0 => decomp338GreedyStep h Y t 0
  | i + 1 => decomp338GreedyStep h Y (decomp338GreedyCutoff h Y t i) (i + 1)

/-- Auxiliary endpoint bounds for second memoir pages 109 to 111.
A nonempty bounded greedy search stays between its endpoints and obeys the target mass. -/
lemma decomp338_greedy_step_bounds (h Y w i : ℕ) (hYw : Y ≤ w) :
    Y ≤ decomp338GreedyStep h Y w i ∧ decomp338GreedyStep h Y w i ≤ w ∧
      (∑ p ∈ (Ioc (decomp338GreedyStep h Y w i) w).filter Nat.Prime, nuN h p) ≤
        (decomp305HeadMass i : ℝ) / 100 := by
  have hex : ∃ y : ℕ, Y ≤ y ∧ y ≤ w ∧
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ (decomp305HeadMass i : ℝ) / 100 :=
    ⟨w, hYw, le_rfl, by simpa using (decomp338_head_mass_pos i).le⟩
  unfold decomp338GreedyStep
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- Auxiliary decreasing endpoint bounds for second memoir pages 109 to 111.
Every greedy cutoff remains above its fixed residual endpoint. -/
lemma decomp338_greedy_cutoff_bounds (h Y t : ℕ) (hYt : Y ≤ t) :
    Antitone (decomp338GreedyCutoff h Y t) ∧
      (∀ i, Y ≤ decomp338GreedyCutoff h Y t i) ∧ decomp338GreedyCutoff h Y t 0 ≤ t := by
  have hlo (i : ℕ) : Y ≤ decomp338GreedyCutoff h Y t i := by
    induction i with
    | zero => exact (decomp338_greedy_step_bounds h Y t 0 hYt).1
    | succ i ih => exact (decomp338_greedy_step_bounds h Y _ (i + 1) ih).1
  refine ⟨antitone_nat_of_succ_le ?_, hlo, (decomp338_greedy_step_bounds h Y t 0 hYt).2.1⟩
  intro i
  exact (decomp338_greedy_step_bounds h Y _ (i + 1) (hlo i)).2.1

end
end LeanLab.Ricci1937
