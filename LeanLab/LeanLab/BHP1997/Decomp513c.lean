/-
P0069 page 11, the finite p-norm and supremum notation of Section 3.
This file specializes the existing Mathlib PiLp norm to a finite sample set.
It adds no analytic hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165

namespace LeanLab.BHP1997.Decomp513c

/-- P0069 page 11, the norm notation before display 3.2.
Use the Mathlib PiLp norm on the actual finite sample subtype.
The paper uses finite real orders at least one and the top order for its supremum norm. -/
noncomputable def sampleLp {α : Type*} (S : Finset α) (f : α → ℂ) (p : ENNReal) : ℝ := by
  classical
  exact ‖(WithLp.toLp p (fun j : S => f j) : PiLp p (fun _ : S => ℂ))‖

/-- P0069 page 11, the finite sample norm notation before display 3.2.
This identification uses the existing Mathlib PiLp norm. -/
theorem sampleLp_eq_sum {α : Type*} (S : Finset α) (f : α → ℂ)
    {p : ℝ} (hp : 1 ≤ p) :
    sampleLp S f (ENNReal.ofReal p) = (∑ j ∈ S, ‖f j‖ ^ p) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  unfold sampleLp
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp0.le] using hp0)]
  simp only [ENNReal.toReal_ofReal hp0.le]
  change (∑ j : S, ‖f j‖ ^ p) ^ (1 / p) = _
  exact congrArg (fun z : ℝ => z ^ (1 / p)) (Finset.sum_coe_sort S (fun j => ‖f j‖ ^ p))


/-- P0069 page 11, the finite sample norm notation before display 3.2.
This identification uses the existing Mathlib PiLp norm. -/
theorem sampleLp_one {α : Type*} (S : Finset α) (f : α → ℂ) :
    sampleLp S f 1 = ∑ j ∈ S, ‖f j‖ := by
  simpa using sampleLp_eq_sum S f (p := 1) (by norm_num)


/-- P0069 page 11, the finite sample norm notation before display 3.2.
This identification uses the existing Mathlib PiLp norm. -/
theorem sampleLp_two_sq {α : Type*} (S : Finset α) (f : α → ℂ) :
    sampleLp S f 2 ^ 2 = ∑ j ∈ S, ‖f j‖ ^ 2 := by
  classical
  unfold sampleLp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_coe_sort S (fun j => ‖f j‖ ^ 2)


/-- P0069 page 11, the finite sample norm notation before display 3.2.
This identification uses the existing Mathlib PiLp norm. -/
theorem sampleLp_top {α : Type*} (S : Finset α) (f : α → ℂ) :
    sampleLp S f (⊤ : ENNReal) = ⨆ j : S, ‖f j‖ := by
  rfl

end LeanLab.BHP1997.Decomp513c
