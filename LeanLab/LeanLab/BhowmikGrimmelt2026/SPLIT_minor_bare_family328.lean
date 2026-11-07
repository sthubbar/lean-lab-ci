/-
Split of the bare minor family estimate `minor_bare_family328` of Decomp328b.

The family second moment of the bare minor coefficient is already available with logarithm
power nine. Its power part is already the target power part: `(X^2/R + X^(8/5)) * X` equals
`(R^-1 + X^(-2/5)) * X^3` with `R = X^ϑ`. The whole gap to logarithm power five therefore
sits in the pointwise minor arc bound for the prime sum, which the available route supplies
with logarithm power four and the target needs with logarithm power two.

The leaves are: the sharper pointwise bound for the unsmoothed sum, its transfer through the
smoothing by parts to the smoothed sum, and the power bookkeeping that rewrites the power
nine expression into the printed power part.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp328b

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. The minor arc bound for the unsmoothed prime sum at logarithm power two:
on a minor arc at length `X` nothing above the rational scale `√R` survives, so every partial
sum up to `X` is bounded by `(X/√R + X^(4/5))` times the square of the logarithm of `X`.
This is the pointwise sharpening that the available power four bound does not give. -/
theorem split_leaf_ssum_minor_log2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ), 2 ≤ X → ∀ R : ℝ, 1 ≤ R → R ≤ X →
      ∀ (m : ℕ), m ≤ X → ∀ α : ℝ, ¬ MajorArc X R α →
        ‖Ssum m α‖ ≤ C * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) *
          Real.log X ^ 2 := by
  sorry

/-- LEAF. The same minor arc bound after the smoothing by parts, for the smoothed prime sum:
summation by parts against the Lipschitz smoothing transfers the power two bound for the
unsmoothed partial sums to the smoothed sum, with a constant absorbing the Lipschitz constant
and the support of the weight. -/
theorem split_leaf_sphi_minor_log2 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ), 2 ≤ X → ∀ R : ℝ, 1 ≤ R → R ≤ X →
      ∀ (N : ℕ), N ≤ X → ∀ α : ℝ, ¬ MajorArc X R α →
        ‖Sphi ϕ N α‖ ≤ C * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) *
          Real.log X ^ 2 := by
  sorry

/-- LEAF. The power bookkeeping identity: at `R = X ^ ϑ` the power part of the logarithm
power nine estimate, namely `(X^2/R + X^(8/5)) * X`, is exactly the target power part
`(R⁻¹ + X^(-(2/5))) * X^3`. This uses only that two real powers of a positive base add. -/
theorem split_leaf_power_identity (X : ℕ) (hX : 2 ≤ X) (ϑ : ℝ) :
    ((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * (X : ℝ) =
      (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 := by
  sorry

/-- The bare minor family has the printed power budget with logarithm power five, assembled
from the three leaves above and the fixed scale family second moment. -/
theorem minor_bare_family328_split {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  obtain ⟨C₀, hC₀, hsup0⟩ := split_leaf_sphi_minor_log2 hϕ
  refine ⟨192 * C₀ ^ 2 * (L : ℝ) ^ 2, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC₀ 2))
      (pow_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ)) 2)
  intro X hX
  let R : ℝ := (X : ℝ) ^ ϑ
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < R := by linarith
  have hRX : R ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = _ := Real.rpow_one _
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else 1
  let U : ℝ := C₀ * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 2
  have hW : Measurable W :=
    measurable_const.ite (measurableSet_majorArc84 X R) measurable_const
  have hWB (α : ℝ) : ‖W α‖ ≤ (1 : ℝ) := by
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  have hU0 : 0 ≤ U := by
    have hA : (0 : ℝ) ≤ (X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ) := by positivity
    have hl : (0 : ℝ) ≤ Real.log X ^ 2 := by positivity
    dsimp [U]
    exact mul_nonneg (mul_nonneg hC₀ hA) hl
  have hsup (n : ℕ) (hn : n ≤ X) (α : ℝ) (hne : W α ≠ 0) : ‖Sphi ϕ n α‖ ≤ U := by
    have hm : ¬ MajorArc X R α := by
      intro hh
      exact hne (by simp [W, hh])
    exact hsup0 X hX R hR1 hRX n hn α hm
  have hfam := supported_family_sharp261 hϕ hL hX hW (by norm_num : (0 : ℝ) ≤ 1) hU0 hWB hsup
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) =
      minorBare328 ϕ X N ϑ := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hm : MajorArc X R α <;> simp [W, minorBare328, R, hm]
  have hA2 : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hRp.le]
  have hD2 : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
    norm_num
  have hsq : ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 ≤
      2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← hA2, ← hD2]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  simp_rw [heq] at hfam
  have hlogX : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  calc
    _ ≤ 96 * (1 : ℝ) ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X := hfam
    _ = 96 * C₀ ^ 2 * (L : ℝ) ^ 2 *
        ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 * X * Real.log X ^ 5 := by
      dsimp [U]
      ring
    _ ≤ 96 * C₀ ^ 2 * (L : ℝ) ^ 2 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 5 := by
      gcongr
    _ = 192 * C₀ ^ 2 * (L : ℝ) ^ 2 *
        (((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) * (X : ℝ)) * Real.log X ^ 5 := by
      ring
    _ = 192 * C₀ ^ 2 * (L : ℝ) ^ 2 *
        (((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3)) *
          Real.log X ^ 5 := by
      dsimp [R]
      rw [split_leaf_power_identity X hX ϑ]
    _ = _ := by
      ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.split_leaf_ssum_minor_log2
#print axioms LeanLab.BhowmikGrimmelt2026.split_leaf_sphi_minor_log2
#print axioms LeanLab.BhowmikGrimmelt2026.split_leaf_power_identity
#print axioms LeanLab.BhowmikGrimmelt2026.minor_bare_family328_split
