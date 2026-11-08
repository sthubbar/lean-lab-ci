/-
Exact frequency support of the smaller leaf in Decomp461a.
Source: P0029 page 26 displays 7.4 to 7.7 and page 27 display 7.8.
The small denominator region is removed as an actual integral.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp461a

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The pure continuous off rational coefficient has an integrable major arc integrand. -/
theorem offRational_integrable461 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {X : ℕ} (hX : 2 ≤ X) (N : ℕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
    IntervalIntegrable
      (fun α => {α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
        (fun α => Sphi ϕ N α ^ 2 *
          (nearContinuous432 G X ((X : ℝ) ^ ϑ) η α -
            continuousModel405 G ((X : ℝ) ^ ϑ)
              (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α)
      volume 0 1 := by
  have hf := (continuousTail_integrable432 hϕ hG hX N ϑ hϑ hη hscale).sub
    (centralAlias_integrable432 hϕ hG hX N ϑ hϑ hη hη1 hscale)
  apply hf.congr
  intro α hα
  have hα' : α ∈ Set.Icc (0 : ℝ) 1 := by
    exact Set.Ioc_subset_Icc_self (by simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα)
  by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α
  · simp [centralAliasMultiplier432, Set.indicator, hm, hα']
    ring
  · simp [centralAliasMultiplier432, Set.indicator, hm]

/-- The removed small denominator coefficient also has an integrable defining function. -/
theorem smallDen_integrable461 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {X : ℕ} (hX : 2 ≤ X) (N : ℕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
    IntervalIntegrable (fun α => Sphi ϕ N α ^ 2 *
      smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α * ee (-(N * α))) volume 0 1 := by
  obtain ⟨D, hD, hb⟩ := small_denominator_multiplier461 hG ϑ hϑ
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hMb : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left M 0)
  have hLp := smoothed_multiplier_memLp261 (le_max_right M 0) hMb
    (measurable_smallDenMultiplier461 hG X _ η) (by positivity : 0 ≤ D * η ^ 2)
    (hb X hX η hη hη1 hscale) N
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (hLp.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  exact hi.mul_continuousOn
    (ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)).continuousOn

/-- The smaller leaf is exactly the integral on central arcs with no small denominator.
The subtracted region is removed before taking any norm or family sum. -/
theorem large_denominator_integral461 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {X : ℕ} (hX : 2 ≤ X) (N : ℕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
    offRational432 ϕ G X N ϑ η - smallDenCoefficient461 ϕ G X N ϑ η =
      ∫ α in (0 : ℝ)..1,
        {α : ℝ | ¬ ∃ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ϑ⌋₊,
          ∃ a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1),
            (q : ℝ) ≤ Real.sqrt ((X : ℝ) ^ ϑ) ∧
              |α - (a : ℝ) / q| ≤ (X : ℝ) ^ ϑ / ((q : ℝ) * X)}.indicator
          (fun α => {α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearContinuous432 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α) α := by
  classical
  rw [offRational_eq_integral432 hϕ hG hX N ϑ hϑ hη hη1 hscale,
    smallDenCoefficient461, ← intervalIntegral.integral_sub
      (offRational_integrable461 hϕ hG hX N ϑ hϑ hη hη1 hscale)
      (smallDen_integrable461 hϕ hG hX N ϑ hϑ hη hη1 hscale)]
  apply intervalIntegral.integral_congr
  intro α hα
  have hα' : α ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXp ϑ
  by_cases hs : ∃ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ϑ⌋₊,
      ∃ a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1),
        (q : ℝ) ≤ Real.sqrt ((X : ℝ) ^ ϑ) ∧
          |α - (a : ℝ) / q| ≤ (X : ℝ) ^ ϑ / ((q : ℝ) * X)
  · obtain ⟨q, hq, a, ha, hden, hclose⟩ := hs
    have hqn := Finset.mem_Icc.mp hq
    have hqR : (q : ℝ) ≤ (X : ℝ) ^ ϑ :=
      (by exact_mod_cast hqn.2 : (q : ℝ) ≤ ⌊(X : ℝ) ^ ϑ⌋₊).trans (Nat.floor_le hRp.le)
    have hm : MajorArc X ((X : ℝ) ^ ϑ) α :=
      ⟨q, hqn.1, hqR, a, (Finset.mem_filter.mp ha).2, hclose⟩
    have hs' : ∃ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ϑ⌋₊,
        ∃ a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1),
          (q : ℝ) ≤ Real.sqrt ((X : ℝ) ^ ϑ) ∧
            |α - (a : ℝ) / q| ≤ (X : ℝ) ^ ϑ / ((q : ℝ) * X) :=
      ⟨q, hq, a, ha, hden, hclose⟩
    simp only [smallDenMultiplier461, Set.indicator, Set.mem_setOf_eq, hα', hs', hm,
      true_and, ite_true, not_true_eq_false, ite_false]
    ring
  · simp only [smallDenMultiplier461, Set.indicator, Set.mem_setOf_eq, hα', hs,
      true_and, ite_false, not_false_eq_true, ite_true, mul_zero, zero_mul, sub_zero]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.offRational_integrable461
#print axioms LeanLab.BhowmikGrimmelt2026.smallDen_integrable461
#print axioms LeanLab.BhowmikGrimmelt2026.large_denominator_integral461
