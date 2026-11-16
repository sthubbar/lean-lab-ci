/-
P0069, Section 5, page 51, display 5.17.
Variation bookkeeping for the remaining mixed exponent integrals.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentBV517

namespace LeanLab.BHP1997.LowerShortC165
open Classical MeasureTheory
open scoped BigOperators

/-- Page 51 display 5.17. A bounded function, zero off its active region,
has a smooth step error plus the active indicator jump cost. -/
theorem four_exponent_piecewise_step (f : ℝ → ℝ) (P : ℝ → Prop) {K M : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M)
    (hz : ∀ x, ¬ P x → f x = 0)
    (hlip : ∀ u v, P u → P v → |f v-f u| ≤ K*|v-u|) (u v : ℝ) :
    |f v-f u| ≤ K*|v-u| + M*|(if P v then (1 : ℝ) else 0)-(if P u then (1 : ℝ) else 0)| := by
  by_cases hu : P u
  · by_cases hv : P v
    · simpa only [if_pos hu, if_pos hv, sub_self, abs_zero, mul_zero, add_zero] using hlip u v hu hv
    · rw [hz v hv, zero_sub, abs_neg, if_neg hv, if_pos hu]
      norm_num
      nlinarith [hf u, mul_nonneg hK (abs_nonneg (v-u))]
  · by_cases hv : P v
    · rw [hz u hu, sub_zero, if_pos hv, if_neg hu]
      norm_num
      nlinarith [hf v, mul_nonneg hK (abs_nonneg (v-u))]
    · rw [hz u hu, hz v hv, if_neg hu, if_neg hv]
      simp only [sub_self, abs_zero, mul_zero, add_zero]
      exact mul_nonneg hK (abs_nonneg _)

/-- Page 51 display 5.17. A smooth step bound and a finite indicator jump
bound give a quantitative total variation bound on any monotone partition. -/
theorem four_exponent_piecewise_variation (f : ℝ → ℝ) (P : ℝ → Prop) {K M J : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M)
    (hz : ∀ x, ¬ P x → f x = 0)
    (hlip : ∀ u v, P u → P v → |f v-f u| ≤ K*|v-u|)
    (e : ℕ → ℝ) (he : Monotone e) {lo hi : ℕ} (hlo : lo ≤ hi)
    (hj : (∑ i ∈ Finset.Ico lo hi,
      |(if P (e (i+1)) then (1 : ℝ) else 0)-(if P (e i) then (1 : ℝ) else 0)|) ≤ J) :
    (∑ i ∈ Finset.Ico lo hi, |f (e (i+1))-f (e i)|) ≤ K*(e hi-e lo)+M*J := by
  calc _ ≤ ∑ i ∈ Finset.Ico lo hi, (K*|e (i+1)-e i| +
        M*|(if P (e (i+1)) then (1 : ℝ) else 0)-(if P (e i) then (1 : ℝ) else 0)|) :=
      Finset.sum_le_sum (fun i _ => four_exponent_piecewise_step f P hK hM hf hz hlip _ _)
    _ = K*(e hi-e lo) + M*(∑ i ∈ Finset.Ico lo hi,
        |(if P (e (i+1)) then (1 : ℝ) else 0)-(if P (e i) then (1 : ℝ) else 0)|) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      congr 1
      congr 1
      have habs : ∀ i : ℕ, |e (i+1)-e i| = e (i+1)-e i := fun i =>
        abs_of_nonneg (sub_nonneg.mpr (he (Nat.le_add_right i 1)))
      simp only [habs]
      exact Finset.sum_Ico_sub (f := e) hlo
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hj hM)

/-- Page 51 display 5.17. Integrating an inner coordinate multiplies a
uniform partition variation bound by the inner interval length. -/
theorem four_exponent_integral_partition_variation (φ : ℝ → ℝ → ℝ)
    (e : ℕ → ℝ) (S : Finset ℕ) {l r V : ℝ} (hlr : l ≤ r)
    (hi : ∀ x, IntervalIntegrable (φ x) volume l r)
    (hv : ∀ t ∈ Set.Icc l r, (∑ i ∈ S, |φ (e (i+1)) t-φ (e i) t|) ≤ V) :
    (∑ i ∈ S, |(∫ t in l..r, φ (e (i+1)) t)-(∫ t in l..r, φ (e i) t)|) ≤ V*(r-l) := by
  have hia : ∀ i ∈ S, IntervalIntegrable
      (fun t => |φ (e (i+1)) t-φ (e i) t|) volume l r :=
    fun i _ => ((hi _).sub (hi _)).abs
  have his : IntervalIntegrable (fun t => ∑ i ∈ S, |φ (e (i+1)) t-φ (e i) t|) volume l r := by
    convert IntervalIntegrable.sum S hia using 1
    ext t
    simp only [Finset.sum_apply]
  calc _ ≤ ∑ i ∈ S, ∫ t in l..r, |φ (e (i+1)) t-φ (e i) t| := by
        apply Finset.sum_le_sum
        intro i hiS
        rw [← intervalIntegral.integral_sub (hi _) (hi _)]
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm
            (f := fun t => φ (e (i+1)) t-φ (e i) t) hlr)
    _ = ∫ t in l..r, ∑ i ∈ S, |φ (e (i+1)) t-φ (e i) t| :=
      (intervalIntegral.integral_finsetSum hia).symm
    _ ≤ ∫ _t in l..r, V :=
      intervalIntegral.integral_mono_on hlr his intervalIntegrable_const hv
    _ = V*(r-l) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- Page 51 display 5.17. A uniform bound on all monotone partition sums
is a bound on Mathlib extended total variation. -/
theorem four_exponent_evariation_of_partition_bound (f : ℝ → ℝ) (l r V : ℝ)
    (h : ∀ e : ℕ → ℝ, Monotone e → (∀ i, e i ∈ Set.Icc l r) → ∀ n : ℕ,
      (∑ i ∈ Finset.range n, |f (e (i+1))-f (e i)|) ≤ V) :
    eVariationOn f (Set.Icc l r) ≤ ENNReal.ofReal V := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, e, he, hmem⟩
  simp only [edist_dist, Real.dist_eq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (h e he hmem n)

#print axioms four_exponent_piecewise_step
#print axioms four_exponent_piecewise_variation
#print axioms four_exponent_integral_partition_variation
#print axioms four_exponent_evariation_of_partition_bound
end LeanLab.BHP1997.LowerShortC165
