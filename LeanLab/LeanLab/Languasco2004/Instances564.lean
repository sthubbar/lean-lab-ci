/-
Jia 1996 Lemma 27, nonvacuity checks for the new arithmetic transfer data.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
These are definition and source table instances, not range extension computations.
-/
import LeanLab.Languasco2004.Model564
import LeanLab.Languasco2004.RemainderData564

namespace LeanLab.Languasco2004.Instances564
open Real Finset Model564 RemainderData564
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 263 display 48: the integer 35 survives in B at Y equal to 20. -/
theorem roughCount_positive_instance : 0 < roughCount 20 35 5 := by
  unfold roughCount
  apply card_pos.mpr
  refine ⟨35, mem_filter.mpr ⟨by norm_num, by norm_num, ?_⟩⟩
  intro p hp hplt hpd
  have hpL := hp.two_le
  have hpU : p < 5 := by exact_mod_cast hplt
  interval_cases p <;> norm_num at *

/-- Pages 270 and 280: empty source families have exactly zero model mass. -/
theorem empty_models (N Y : ℝ) (n : ℕ) :
    roughModel ∅ Y = 0 ∧ primeModel ∅ N Y n = 0 := by
  simp [roughModel, primeModel]

/-- Pages 281 and 282: every printed numerical subdomain has a strict rational interior. -/
theorem row_interior : ∀ i : Fin 16,
    let r := numericData i
    let t := (r 0+r 1)/2
    let u := (r 2+r 3*t+r 4+r 5*t)/2
    r 0 < t ∧ t < r 1 ∧ r 2+r 3*t < u ∧ u < r 4+r 5*t := by
  decide +kernel

/-- Pages 270 and 280: the finite transfer applies to nonempty failure sets. -/
theorem bad_transfer_instance :
    ((({0} : Finset ℕ).filter (fun _ => (0:ℝ) < 1*1)).card = 1) ∧
    ((({0} : Finset ℕ).filter (fun _ => (0:ℝ)+1*1 < 3)).card = 1) ∧
    ({0} : Finset ℕ).filter (fun _ => (0:ℝ) < 1*1) ⊆
      ({0} : Finset ℕ).filter (fun _ => (0:ℝ)+1*1 < 3) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact bad_transfer {0} (fun _ => 0) (fun _ => 1) (fun _ => 3) 1 1
    (by intro n hn; norm_num)

/-- Pages 208 and 280: positive tolerance and sufficiently small epsilon domains are inhabited. -/
theorem transfer_parameter_instance (e : ℝ) (he : 0 < e) :
    (0:ℝ) < 1/20000000 ∧ 0 < e/2 ∧ e/2 < e ∧ (0:ℝ) < 1 := by
  constructor
  · norm_num
  constructor
  · positivity
  constructor
  · linarith
  · norm_num

#print axioms roughCount_positive_instance
#print axioms empty_models
#print axioms row_interior
#print axioms bad_transfer_instance
#print axioms transfer_parameter_instance
end
end LeanLab.Languasco2004.Instances564
