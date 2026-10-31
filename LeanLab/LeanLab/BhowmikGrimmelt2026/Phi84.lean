/-
A concrete smoothing weight for page 25 display 7.1.
The symmetric bump is normalized by the square root of its positive squared mass.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- A fixed smooth bump centered at zero with radii one tenth and one fifth. -/
noncomputable def phiBump84 : ContDiffBump (0 : ℝ) where
  rIn := 1 / 10
  rOut := 1 / 5
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Shift the fixed bump to be centered at one half. -/
noncomputable def phiBase84 (x : ℝ) : ℝ := phiBump84 (x - 1 / 2)

/-- Page 25 display 7.1. The fixed bump has support strictly inside the permitted interval. -/
theorem phiBase84_support : tsupport phiBase84 ⊆ Set.Icc (3 / 10) (7 / 10) := by
  change closure (Function.support phiBase84) ⊆ _
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hb : x - 1 / 2 ∈ Function.support (phiBump84 : ℝ → ℝ) := hx
  have hball : x - 1 / 2 ∈ Metric.ball (0 : ℝ) (1 / 5) := by
    rw [phiBump84.support_eq] at hb
    exact hb
  have ha : |x - 1 / 2| < 1 / 5 := by simpa [Real.dist_eq] using hball
  constructor <;> linarith [(abs_lt.mp ha).1, (abs_lt.mp ha).2]

/-- Page 25 display 7.1. The fixed bump is symmetric about one half. -/
theorem phiBase84_reflection (x : ℝ) : phiBase84 (1 - x) = phiBase84 x := by
  unfold phiBase84
  rw [show 1 - x - 1 / 2 = -(x - 1 / 2) by ring, phiBump84.neg]

/-- Page 25 display 7.1. The fixed squared bump has strictly positive total mass. -/
theorem phiBase84_mass_pos : 0 < ∫ x : ℝ, phiBase84 x ^ 2 := by
  have hc : Continuous (fun x : ℝ => phiBase84 x ^ 2) :=
    (phiBump84.continuous.comp (continuous_id.sub continuous_const)).pow 2
  have hs : HasCompactSupport (fun x : ℝ => phiBase84 x ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (3 / 10 : ℝ) (7 / 10))
      isCompact_Icc
    intro x hx
    have hb : phiBase84 x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    exact phiBase84_support (subset_tsupport phiBase84 hb)
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs (fun x => sq_nonneg _)
    (x := 1 / 2)
  change phiBump84 ((1 / 2 : ℝ) - 1 / 2) ^ 2 ≠ 0
  rw [sub_self, phiBump84.one_of_mem_closedBall]
  · norm_num
  · simp [phiBump84]

/-- Normalize the symmetric bump by the square root of its squared mass. -/
noncomputable def phiWeight84 (x : ℝ) : ℝ :=
  (Real.sqrt (∫ y : ℝ, phiBase84 y ^ 2))⁻¹ * phiBase84 x

/-- Page 25 display 7.1. The normalized fixed bump is a concrete admissible smoothing weight. -/
theorem phiWeight84_isPhi : IsPhi phiWeight84 := by
  let J : ℝ := ∫ y : ℝ, phiBase84 y ^ 2
  have hJ : 0 < J := phiBase84_mass_pos
  have hsub : Function.support phiWeight84 ⊆ Function.support phiBase84 := by
    intro x hx
    intro hb
    exact hx (by simp [phiWeight84, hb])
  have htop : tsupport phiWeight84 ⊆ Set.Icc (3 / 10 : ℝ) (7 / 10) := by
    have ht : tsupport phiWeight84 ⊆ tsupport phiBase84 := closure_mono hsub
    exact ht.trans phiBase84_support
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (phiBump84.contDiff.comp (contDiff_id.sub contDiff_const))
  · intro x
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) phiBump84.nonneg
  · exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun x hx => htop (subset_tsupport phiWeight84 hx))
  · intro x hx
    have h := htop hx
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · have hint : (∫ x in (0 : ℝ)..1, phiBase84 x ^ 2) = J := by
      apply intervalIntegral.integral_eq_integral_of_support_subset
      intro x hx
      have hb : phiBase84 x ≠ 0 := by intro hz; exact hx (by simp [hz])
      have h := phiBase84_support (subset_tsupport phiBase84 hb)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    change (∫ t in (0 : ℝ)..1,
      ((Real.sqrt J)⁻¹ * phiBase84 t) * ((Real.sqrt J)⁻¹ * phiBase84 (1 - t))) = 1
    simp_rw [phiBase84_reflection]
    calc
      _ = (Real.sqrt J)⁻¹ ^ 2 * (∫ t in (0 : ℝ)..1, phiBase84 t ^ 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = 1 := by rw [hint, inv_pow, Real.sq_sqrt hJ.le, inv_mul_cancel₀ hJ.ne']

/-- Page 25 display 7.1. The constructed weight is positive at its center. -/
theorem phiWeight84_center_pos : 0 < phiWeight84 (1 / 2) := by
  unfold phiWeight84
  apply mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr phiBase84_mass_pos))
  change 0 < phiBump84 ((1 / 2 : ℝ) - 1 / 2)
  rw [sub_self, phiBump84.one_of_mem_closedBall]
  · norm_num
  · simp [phiBump84]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.phiBase84_support

#print axioms LeanLab.BhowmikGrimmelt2026.phiBase84_reflection

#print axioms LeanLab.BhowmikGrimmelt2026.phiBase84_mass_pos

#print axioms LeanLab.BhowmikGrimmelt2026.phiWeight84_isPhi

#print axioms LeanLab.BhowmikGrimmelt2026.phiWeight84_center_pos
