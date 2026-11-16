/-
The initial interval in P0088 page 8 after display 31 needs a separate input.
A singleton at the lower endpoint has positive initial energy and zero bulk
energy. This is a limitation of a general window argument, not a claim about
the paper's particular rough coefficients.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Gallagher634

namespace LeanLab.KumchevLiu2007.Task634

open Real Complex MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 8 after display 31: a general window estimate cannot transfer
the bulk energy to the initial interval without information on coefficients. -/
theorem singleton_endpoint_energy (H : ℝ) (hH : 0 < H) :
    let S : ℝ → ℂ := fun t =>
      ∑ _m ∈ ({1} : Finset ℕ).filter
        (fun m => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), (1 : ℂ)
    (∫ t in (1 - H)..1, ‖S t‖ ^ 2) = H ∧
      (∫ t in (1 : ℝ)..2, ‖S t‖ ^ 2) = 0 := by
  dsimp only
  constructor
  · calc
      _ = ∫ _t in (1 - H)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        have htH : (1 : ℝ) ≤ t + H := by linarith [ht.1]
        simp [Finset.filter_singleton, ht.2, htH]
      _ = H := by simp
  · calc
      _ = ∫ _t in (1 : ℝ)..2, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro t ht
        have ht1 : ¬t < (1 : ℝ) := by linarith [ht.1]
        simp [Finset.filter_singleton, ht1]
      _ = 0 := by simp

end LeanLab.KumchevLiu2007.Task634

#print axioms LeanLab.KumchevLiu2007.Task634.singleton_endpoint_energy
