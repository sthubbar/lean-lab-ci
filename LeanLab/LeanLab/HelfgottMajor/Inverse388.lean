import Mathlib

/-!
Finite partial summation for inverse heights, used in P0014 page 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.HelfgottMajor.Inverse388
open Real MeasureTheory intervalIntegral

/-- Finite partial summation with a supplied linear counting bound.
Source P0014 page 38, proof of Lemma 4.3.
-/
theorem reciprocal_sum_le_of_count {ι : Type*} (s : Finset ι) (x w : ι → ℝ)
    (T a b : ℝ) (hT : 1 ≤ T)
    (hx : ∀ i ∈ s, 1 < x i ∧ x i ≤ T)
    (hcount : ∀ t : ℝ, 1 ≤ t → t ≤ T →
      (∑ i ∈ s, if x i ≤ t then w i else 0) ≤ a * t + b) :
    (∑ i ∈ s, w i / x i) ≤ a * (1 + log T) + b := by
  classical
  have hT0 : 0 < T := by linarith
  have hbase (c : ℝ) : IntervalIntegrable (fun t : ℝ => c / t ^ 2) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    have ht' : 1 ≤ t := (Set.uIcc_of_le hT ▸ ht).1
    change t ^ 2 ≠ 0
    have : 0 < t := by linarith
    positivity
  have hderiv (c t : ℝ) (ht : t ≠ 0) :
      HasDerivAt (fun t : ℝ => -(c / t)) (c / t ^ 2) t := by
    convert (hasDerivAt_inv ht).const_mul (-c) using 1
    · funext y; simp only [div_eq_mul_inv]; ring
    · simp only [div_eq_mul_inv]; ring
  have hkernel (c y : ℝ) (hy : 1 ≤ y) (hyT : y ≤ T) :
      (∫ t in y..T, c / t ^ 2) = c / y - c / T := by
    have hint : IntervalIntegrable (fun t : ℝ => c / t ^ 2) volume y T := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_const.div (continuousOn_id.pow 2)
      intro t ht
      have ht' : y ≤ t := (Set.uIcc_of_le hyT ▸ ht).1
      have : 0 < t := by linarith
      change t ^ 2 ≠ 0
      positivity
    have h := integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv c t (by have := (Set.uIcc_of_le hyT ▸ ht).1; linarith)) hint
    simpa [sub_eq_add_neg, add_comm] using h
  let f : ι → ℝ → ℝ := fun i t => Set.indicator (Set.Ici (x i))
    (fun t : ℝ => w i / t ^ 2) t
  have hfi (i : ι) : IntervalIntegrable (f i) volume 1 T := by
    exact ⟨(hbase (w i)).1.indicator measurableSet_Ici,
      (hbase (w i)).2.indicator measurableSet_Ici⟩
  have hidentity (i : ι) (hi : i ∈ s) :
      (∫ t in (1 : ℝ)..T, f i t) = w i / x i - w i / T := by
    rw [integral_of_le hT]
    change (∫ t in Set.Ioc (1 : ℝ) T,
      Set.indicator (Set.Ici (x i)) (fun t : ℝ => w i / t ^ 2) t) = _
    rw [MeasureTheory.integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    have hset : Set.Ici (x i) ∩ Set.Ioc (1 : ℝ) T = Set.Icc (x i) T := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, (hx i hi).1.trans_le h1, h2⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← integral_of_le (hx i hi).2]
    exact hkernel (w i) (x i) (hx i hi).1.le (hx i hi).2
  have hsumint : (∫ t in (1 : ℝ)..T, ∑ i ∈ s, f i t) =
      (∑ i ∈ s, w i / x i) - (∑ i ∈ s, w i / T) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hfi i)]
    calc
      _ = ∑ i ∈ s, (w i / x i - w i / T) := Finset.sum_congr rfl hidentity
      _ = _ := Finset.sum_sub_distrib _ _
  have hai : IntervalIntegrable (fun t : ℝ => a / t) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro t ht
    have := (Set.uIcc_of_le hT ▸ ht).1
    change t ≠ 0
    linarith
  have hgi := hai.add (hbase b)
  have hbound : (∫ t in (1 : ℝ)..T, ∑ i ∈ s, f i t) ≤
      ∫ t in (1 : ℝ)..T, (a / t + b / t ^ 2) := by
    have hsumI : IntervalIntegrable (fun t : ℝ => ∑ i ∈ s, f i t) volume 1 T := by
      convert (IntervalIntegrable.sum s (fun i _ => hfi i)) using 1
      ext t
      simp
    apply integral_mono_on hT hsumI hgi
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hc := div_le_div_of_nonneg_right (hcount t ht.1 ht.2) (sq_nonneg t)
    have heq : (∑ i ∈ s, f i t) = (∑ i ∈ s, if x i ≤ t then w i else 0) / t ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : x i ≤ t <;> simp [f, Set.indicator, h]
    rw [heq]
    convert hc using 1 <;> field_simp [ne_of_gt ht0]
  have hright : (∫ t in (1 : ℝ)..T, (a / t + b / t ^ 2)) =
      a * log T + b - b / T := by
    rw [integral_add hai (hbase b)]
    have halog : (∫ t in (1 : ℝ)..T, a / t) = a * log T := by
      have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T,
          HasDerivAt (fun t : ℝ => a * log t) (a / t) t := by
        intro t ht
        have ht0 : 0 < t := by have := (Set.uIcc_of_le hT ▸ ht).1; linarith
        simpa [div_eq_mul_inv] using (hasDerivAt_log ht0.ne').const_mul a
      simpa using integral_eq_sub_of_hasDerivAt hd hai
    rw [halog, hkernel b 1 le_rfl hT]
    simp only [div_one]
    ring
  have hboundary := div_le_div_of_nonneg_right (hcount T hT le_rfl) hT0.le
  have hboundary' : (∑ i ∈ s, w i / T) ≤ a + b / T := by
    have heq : (∑ i ∈ s, if x i ≤ T then w i else 0) = ∑ i ∈ s, w i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [(hx i hi).2]
    rw [heq, Finset.sum_div] at hboundary
    convert hboundary using 1 <;> field_simp [hT0.ne']
  rw [hsumint, hright] at hbound
  nlinarith

end LeanLab.HelfgottMajor.Inverse388
