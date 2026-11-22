/-
Split of the major tail family on the multi denominator range.

The target bounds the sum over N up to X of the squared major tail coefficient at
the scale R equal to X to the theta, with eta between the lower scale bound and
one. The proof cuts that family at its multiplier. The tail is the integral over
the major arcs of the smoothed square times the difference between the selected
central transform and the full transform, so the work is:

1. a comparison of the two transforms on a major arc, the single remaining
   multi denominator estimate, with constant independent of X, eta and the arc;
2. the smoothed family mean square for an arbitrary measurable bounded
   multiplier, with the fifth power of the logarithm.

The assembly masks the difference to the unit interval, applies the family
estimate to the masked multiplier and collects the constants.

The family estimate is proved from smoothed_family_bound261.
The pointwise estimate remains open and the assembly is conditional on it.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp525a
import LeanLab.BhowmikGrimmelt2026.MajorArcPair

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-! ## The two estimates -/

/-- LEAF. Multi denominator step: the comparison of the two transforms on a major arc.

For a major weight G and a fixed theta strictly between zero and one half, one
nonnegative constant bounds the distance between the selected central transform
and the full transform by the constant times eta squared, at a point of the unit
interval that lies on a major arc of scale R equal to X to the theta, for every X
at least two with R at least two, every eta in zero one and ten R squared at most
eta X. The bound is uniform in the point, in the arc and in X; only the fixed
central term is retained on the left, and the off rational remainder of the full
transform is what has to be absorbed into the constant. -/
theorem multi_tail_pointwise525 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∀ α ∈ Set.Icc (0 : ℝ) 1, MajorArc X ((X : ℝ) ^ ϑ) α →
      ‖nearTransform525 G X ((X : ℝ) ^ ϑ) η α -
        bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α‖ ≤
        D * η ^ 2 := by
  classical
  obtain ⟨Cg, hCg, hGt⟩ := GThat_bound hG.supp hG.smooth (2 + 2 / ϑ)
  refine ⟨2 * Cg * 5 ^ (-(2 + 2 / ϑ)) * 100, by positivity, ?_⟩
  intro X hX hR η hη hη1 hscale α hα hm
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℕ → ℝ := fun q => η * X * q / R
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hXp ϑ
  have hR0 : 0 ≤ R := hRp.le
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hηX : η * X ≤ X := by nlinarith
  have hsep : 2 * R ^ 2 < X := by
    have h2 : 10 * R ^ 2 ≤ X := by nlinarith
    nlinarith
  have hRX : R ≤ X := by nlinarith [hR1, sq_nonneg (R - 1)]
  have hTpos : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    have hq1 : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    have hqp : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    dsimp [T, R]
    positivity
  obtain ⟨q, hqmem, a, hamem, hclose⟩ := majorArc_center_in_sum525 hXp hRX hα hm
  have hnear := nearTransform_eq525 hXp hR0 hsep hqmem hamem hclose
  rw [hnear, bRhat_eq hG.supp hG.even R T hTpos α]
  sorry

/-- PROVED from smoothed_family_bound261 and log_le_sixteen_log5_525.
The smoothed family mean square with the fifth power of the logarithm.

For an admissible phi, one nonnegative constant bounds the sum over N up to X of
the squared coefficient of the smoothed square times an arbitrary measurable
multiplier by the constant times the square of the multiplier bound, X cubed and
the fifth power of log X, for every X at least two. The multiplier is not
assumed to be continuous and no scale condition enters, so the estimate is the
power five form of the family bound used for every coefficient family of this
page. -/
theorem multi_tail_family525 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ B : ℝ, 0 ≤ B →
      ∀ W : ℝ → ℂ, Measurable W → (∀ α, ‖W α‖ ≤ B) →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))‖ ^ 2 ≤
        C * B ^ 2 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hfamily⟩ := smoothed_family_bound261 hϕ
  refine ⟨16 * C, by positivity, ?_⟩
  intro X hX B hB W hW hWB
  calc
    _ ≤ C * B ^ 2 * (X : ℝ) ^ 3 * Real.log X := hfamily X hX W hW B hB hWB
    _ ≤ C * B ^ 2 * (X : ℝ) ^ 3 * (16 * Real.log X ^ 5) :=
      mul_le_mul_of_nonneg_left (log_le_sixteen_log5_525 hX) (by positivity)
    _ = _ := by ring

/-! ## Assembly -/

/-- CONDITIONAL on multi_tail_pointwise525.
The major tail family on the multi denominator range, from the pointwise input and the proved family bound.

The multiplier is the difference of the two transforms, masked to the major arcs
of the unit interval; the mask is measurable, the pointwise leaf bounds it by the
constant times eta squared, and the family leaf turns that bound into the
displayed budget. -/
theorem major_tail_multi525_split {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorTail525 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨D, hD, hDbound⟩ := multi_tail_pointwise525 hG ϑ hϑ
  obtain ⟨C, hC, hfamily⟩ := multi_tail_family525 hϕ
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro X hX hR η hη hη1 hscale
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : (0 : ℝ) < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXp ϑ
  have hTp : ∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ϑ⌋₊,
      0 < η * X * q / (X : ℝ) ^ ϑ := by
    intro q hq
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    positivity
  let W : ℝ → ℂ := fun α =>
    if α ∈ Set.Icc (0 : ℝ) 1 ∩ {α | MajorArc X ((X : ℝ) ^ ϑ) α} then
      nearTransform525 G X ((X : ℝ) ^ ϑ) η α -
        bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α else 0
  have hW : Measurable W := by
    have hc : Continuous (fun α : ℝ =>
        bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) :=
      continuous_bRhat hG.supp hG.even _ _ hTp
    have hm : Measurable (fun α : ℝ => nearTransform525 G X ((X : ℝ) ^ ϑ) η α -
        bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) :=
      (measurable_nearTransform525 hG.supp hXp hRp hη).sub hc.measurable
    exact hm.ite (measurableSet_Icc.inter (measurableSet_majorArc84 X ((X : ℝ) ^ ϑ)))
      measurable_const
  have hWB : ∀ α : ℝ, ‖W α‖ ≤ D * η ^ 2 := by
    intro α
    by_cases hm : α ∈ Set.Icc (0 : ℝ) 1 ∩ {α | MajorArc X ((X : ℝ) ^ ϑ) α}
    · simp only [W, if_pos hm]
      exact hDbound X hX hR η hη hη1 hscale α hm.1 hm.2
    · simp only [W, if_neg hm, norm_zero]
      exact mul_nonneg hD (by positivity : (0 : ℝ) ≤ η ^ 2)
  have heq (N : ℕ) : majorTail525 ϕ G X N ϑ η =
      ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α)) := by
    rw [majorTail_eq_integral525 ϕ hG hX N ϑ hη]
    apply intervalIntegral.integral_congr
    intro α hα
    have hα' : α ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα
    by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α
    · have hWα : W α = nearTransform525 G X ((X : ℝ) ^ ϑ) η α -
          bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α := by
        simp only [W]
        exact if_pos ⟨hα', hm⟩
      simp only [hWα]
      simp [Set.indicator, hm]
    · have hWα : W α = 0 := by
        simp only [W]
        exact if_neg (fun hc => hm hc.2)
      simp only [hWα]
      simp [Set.indicator, hm]
  have hfam := hfamily X hX (D * η ^ 2)
    (mul_nonneg hD (by positivity : (0 : ℝ) ≤ η ^ 2)) W hW hWB
  simp_rw [← heq] at hfam
  have hcalc : C * (D * η ^ 2) ^ 2 * (X : ℝ) ^ 3 * Real.log X ^ 5 =
      (C * D ^ 2) * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by ring
  rw [hcalc] at hfam
  exact hfam

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.multi_tail_pointwise525
#print axioms LeanLab.BhowmikGrimmelt2026.multi_tail_family525
#print axioms LeanLab.BhowmikGrimmelt2026.major_tail_multi525_split
