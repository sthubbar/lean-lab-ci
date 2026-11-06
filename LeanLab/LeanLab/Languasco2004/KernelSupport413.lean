/-
Elementary support for the local kernel step in PP1993 page 44 display 3.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
AI wrote the Lean code. Goldbach is open.
The coarse integral bound below does not supply a local mass estimate.
-/
import LeanLab.Languasco2004.Decomp413a

namespace LeanLab.Languasco2004.KernelSupport413
open Finset Real MeasureTheory Decomp279b Decomp413a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 44 display 3: the full minor S2 mass without a kernel factor. -/
def totalMass (N Y H B : ℝ) : ℝ :=
  ∫ α in minorDomain N Y H B, ‖secondSum Y α‖ ^ 2

/-- Page 44 display 3: the capped kernel is periodic under integer shifts. -/
theorem kernel_integer_period (H x : ℝ) (k : ℤ) : kernel H (x + k) = kernel H x := by
  unfold kernel
  simp only [round_add_intCast, Int.cast_add, add_sub_add_right_eq_sub, add_left_inj,
    add_right_inj]

/-- Page 44 display 3: every integer is a pole with the explicit cap value. -/
theorem kernel_integer_pole (H : ℝ) (k : ℤ) : kernel H (k : ℝ) = H := by
  simp [kernel]

/-- Page 44 display 3: away from a pole the kernel also has the reciprocal
nearest integer distance bound. -/
theorem kernel_le_inverse (H x : ℝ) (hx : x ≠ (round x : ℤ)) :
    kernel H x ≤ |x - (round x : ℤ)|⁻¹ := by
  simp only [kernel, ite_eq_right hx]
  exact min_le_right _ _

/-- Page 44 display 3: the kernel attains its cap within distance 1/H
of an integer. This is the near pole part of the covering step. -/
theorem kernel_near_pole (H x : ℝ) (hH : 0 < H)
    (hx : |x - (round x : ℤ)| ≤ 1 / H) : kernel H x = H := by
  by_cases hp : x = (round x : ℤ)
  · simp only [kernel, ite_eq_left hp]
  · have hd : 0 < |x - (round x : ℤ)| := abs_pos.mpr (sub_ne_zero.mpr hp)
    have hmul := (le_div_iff₀ hH).mp hx
    have hi : H ≤ |x - (round x : ℤ)|⁻¹ := by
      rw [← one_div, le_div_iff₀ hd]
      nlinarith
    simp only [kernel, ite_eq_right hp, min_eq_left hi]

/-- Page 44 display 3: the unweighted S2 squared norm is integrable
on the entire chosen period, since it is a continuous finite sum. -/
theorem second_mass_integrable (Y H : ℝ) :
    IntegrableOn (fun α : ℝ => ‖secondSum Y α‖ ^ 2) (period H) volume := by
  have hc : Continuous (fun α : ℝ => ‖secondSum Y α‖ ^ 2) := by
    unfold secondSum phase
    fun_prop
  exact hc.integrableOn_Icc

/-- Page 44 display 3: a coarse bound replaces the squared kernel by
H squared. It retains the total mass and does not prove kernel_from_local. -/
theorem kernelMass_le_totalMass (N Y H B ξ : ℝ) (hH : 0 ≤ H) :
    kernelMass N Y H B ξ ≤ H ^ 2 * totalMass N Y H B := by
  have hi := (second_mass_integrable Y H).mono_set
    (show minorDomain N Y H B ⊆ period H from Set.sdiff_subset)
  have hgi : IntegrableOn (fun α : ℝ => H ^ 2 * ‖secondSum Y α‖ ^ 2)
      (minorDomain N Y H B) volume := hi.const_mul _
  have hp : ∀ α : ℝ, ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2 ≤
      H ^ 2 * ‖secondSum Y α‖ ^ 2 := by
    intro α
    have hk := (sq_le_sq₀ (kernel_nonneg hH (2 * (α - ξ))) hH).mpr (kernel_le H (2 * (α - ξ)))
    nlinarith [mul_le_mul_of_nonneg_left hk (sq_nonneg ‖secondSum Y α‖)]
  unfold kernelMass totalMass
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    hgi (Filter.Eventually.of_forall hp)

/-- Page 44 display 3: a finite uniform bound for the kernel integral
always exists when H is nonnegative. This verifies that the bound premise
in coefficient_energy has witnesses without an analytic estimate. -/
theorem kernel_uniform_bound (N Y H B : ℝ) (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ξ : ℝ, kernelMass N Y H B ξ ≤ K := by
  refine ⟨H ^ 2 * totalMass N Y H B, ?_, fun ξ => kernelMass_le_totalMass N Y H B ξ hH⟩
  exact mul_nonneg (sq_nonneg H) (integral_nonneg (fun _ => sq_nonneg _))

/-- The coarse H cubed local covering loss exceeds the required H squared
loss whenever H exceeds one and V is positive. This records the obstruction
to using the cap alone in the local kernel route. -/
theorem coarse_cover_loss (H V : ℝ) (hH : 1 < H) (hV : 0 < V) :
    H ^ 2 * V < H ^ 3 * V := by
  have hpos : 0 < H ^ 2 * V := mul_pos (sq_pos_of_pos (by linarith)) hV
  have h := mul_lt_mul_of_pos_right hH hpos
  nlinarith

/-- Page 44 display 3: the concrete pole, period and near pole instances. -/
theorem kernel_support_instances :
    kernel 4 (2 : ℝ) = 4 ∧ kernel 4 (1 / 8 : ℝ) = 4 ∧
      kernel 4 (3 / 8 : ℝ) ≤ 8 / 3 := by
  refine ⟨by simpa using kernel_integer_pole 4 2, ?_, ?_⟩
  · apply kernel_near_pole <;> norm_num [round_eq]
  · convert kernel_le_inverse 4 (3 / 8) (by norm_num [round_eq]) using 1 <;>
      norm_num [round_eq]

#print axioms kernel_integer_period
#print axioms kernel_integer_pole
#print axioms kernel_le_inverse
#print axioms kernel_near_pole
#print axioms second_mass_integrable
#print axioms kernelMass_le_totalMass
#print axioms kernel_uniform_bound
#print axioms coarse_cover_loss
#print axioms kernel_support_instances
end
end LeanLab.Languasco2004.KernelSupport413
