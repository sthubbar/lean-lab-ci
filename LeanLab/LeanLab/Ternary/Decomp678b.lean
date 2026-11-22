/-
MMS https://arxiv.org/abs/1610.02017v2 page 11 Proposition 5.1.
Uniform derivative bounds for the explicitly chosen smooth reference profile.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp379c

namespace LeanLab.Ternary.MMS.Task678
open MeasureTheory

/-- The fixed unit interval profile used in the permitted choice of g1.
MMS page 11 Proposition 5.1 permits any such smooth profile. -/
noncomputable def referenceProfile (u : ℝ) : ℝ :=
  expNegInvGlue u * expNegInvGlue (1 - u)

/-- The fixed profile is smooth at every order.
Derived verification of the g1 hypothesis on MMS page 11. -/
theorem referenceProfile_contDiff (j : ℕ) : ContDiff ℝ j referenceProfile := by
  exact expNegInvGlue.contDiff.mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

/-- The fixed profile has compact support in the unit interval.
Derived support verification of g1 on MMS page 11. -/
theorem referenceProfile_hasCompactSupport : HasCompactSupport referenceProfile := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  intro u hu
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · simp [referenceProfile, expNegInvGlue.zero_of_nonpos hu.le]
  · simp [referenceProfile, expNegInvGlue.zero_of_nonpos (by linarith : 1 - u ≤ 0)]

/-- Every derivative of the fixed profile has compact support.
Derived verification of the g1 bounds on MMS page 11. -/
theorem referenceProfile_deriv_hasCompactSupport (j : ℕ) :
    HasCompactSupport (iteratedDeriv j referenceProfile) := by
  induction j with
  | zero => simpa using referenceProfile_hasCompactSupport
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- Every fixed derivative of the profile is uniformly bounded.
Derived verification of the g1 bounds on MMS page 11.
The constant depends only on the derivative order. -/
theorem referenceProfile_deriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, |iteratedDeriv j referenceProfile u| ≤ C := by
  obtain ⟨C, hC⟩ := ((referenceProfile_contDiff j).continuous_iteratedDeriv' j).bounded_above_of_compact_support (referenceProfile_deriv_hasCompactSupport j)
  refine ⟨max 1 C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun u => ?_⟩
  exact (hC u).trans (le_max_right _ _)

/-- Derivatives of the rescaled profile have exactly the inverse length factor.
Derived chain rule for MMS page 11 Proposition 5.1. -/
theorem referenceWeight_iteratedDeriv (x : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (Task379.referenceWeight x) t =
      (Task379.referenceLength x)⁻¹ ^ j *
        iteratedDeriv j referenceProfile ((t - x) / Task379.referenceLength x) := by
  have he : Task379.referenceWeight x =
      fun t => (fun u => referenceProfile ((Task379.referenceLength x)⁻¹ * u)) (t - x) := by
    funext t
    simp only [Task379.referenceWeight, referenceProfile, div_eq_inv_mul]
  rw [he, iteratedDeriv_comp_sub_const j
    (fun u : ℝ => referenceProfile ((Task379.referenceLength x)⁻¹ * u)) x,
    iteratedDeriv_comp_const_mul (referenceProfile_contDiff j)]
  simp only [div_eq_inv_mul]

/-- The explicit g1 satisfies all uniform derivative bounds required in Proposition 5.1.
MMS page 11. The constant is fixed before x and the point t. -/
theorem referenceWeight_deriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → ∀ t : ℝ,
      |iteratedDeriv j (Task379.referenceWeight x) t| ≤
        C / Task379.referenceLength x ^ j := by
  obtain ⟨C, hC, hb⟩ := referenceProfile_deriv_bound j
  refine ⟨C, hC, fun x hx t => ?_⟩
  rw [referenceWeight_iteratedDeriv, abs_mul, abs_pow,
    abs_of_pos (inv_pos.mpr (Task379.referenceLength_pos hx))]
  calc
    _ ≤ (Task379.referenceLength x)⁻¹ ^ j * C :=
      mul_le_mul_of_nonneg_left (hb _)
        (pow_nonneg (inv_nonneg.mpr (Task379.referenceLength_pos hx).le) j)
    _ = _ := by rw [inv_pow, div_eq_mul_inv, mul_comm]

/-- The reference normalization is its length times a fixed positive profile mass.
Derived affine substitution for MMS page 11 bottom display. -/
theorem referenceWeight_integral_scale {x : ℝ} (hx : 0 < x) :
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) =
      Task379.referenceLength x * ∫ u in (0 : ℝ)..1, referenceProfile u := by
  change (∫ t in x..(x + Task379.referenceLength x),
    referenceProfile ((t - x) / Task379.referenceLength x)) = _
  rw [intervalIntegral.integral_comp_sub_right
    (fun u => referenceProfile (u / Task379.referenceLength x)) x]
  rw [sub_self, add_sub_cancel_left,
    intervalIntegral.integral_comp_div referenceProfile (Task379.referenceLength_pos hx).ne']
  simp [(Task379.referenceLength_pos hx).ne']

end LeanLab.Ternary.MMS.Task678
