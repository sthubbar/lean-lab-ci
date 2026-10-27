import LeanLab.Romanov.HMean

/-!
# Weighted Mersenne means by finite summation by parts

AI wrote the Lean code. Known mathematics. HBP arXiv math/0201299v2,
page 21, the weighted mean immediately after display 36.
Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.Romanov

open Finset Real
open LeanLab.HeathBrownPuchta.Lemma8Const

/-- The finite summation by parts identity for linear weights. -/
theorem weighted_prefix (F : ℕ → ℝ) (L : ℕ) :
    ∑ l ∈ Icc 1 L, ((L - l : ℕ) : ℝ) * F l =
      ∑ j ∈ range L, ∑ l ∈ Icc 1 j, F l := by
  have hinner : ∀ j ∈ range L,
      ∑ l ∈ Icc 1 j, F l = ∑ l ∈ Icc 1 L, if l ≤ j then F l else 0 := by
    intro j hj
    rw [← sum_filter]
    congr 1
    ext l
    simp only [mem_filter, mem_Icc]
    have hjL := mem_range.mp hj
    omega
  symm
  calc ∑ j ∈ range L, ∑ l ∈ Icc 1 j, F l
      = ∑ j ∈ range L, ∑ l ∈ Icc 1 L, if l ≤ j then F l else 0 := sum_congr rfl hinner
    _ = ∑ l ∈ Icc 1 L, ∑ j ∈ range L, if l ≤ j then F l else 0 := sum_comm
    _ = ∑ l ∈ Icc 1 L, ((L - l : ℕ) : ℝ) * F l := by
        apply sum_congr rfl
        intro l _
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        have he : (range L).filter (fun j => l ≤ j) = Ico l L := by
          ext j
          simp only [mem_filter, mem_range, mem_Ico]
          omega
        rw [he, Nat.card_Ico]

/-- Transfer a square root prefix error to a linearly weighted mean. -/
theorem prefix_error_to_weighted_error (F : ℕ → ℝ) (b C : ℝ) (hC : 0 ≤ C)
    (h : ∀ J : ℕ, |(∑ l ∈ Icc 1 J, F l) - b * J| ≤ C * sqrt (J : ℝ)) (L : ℕ) :
    |(∑ l ∈ Icc 1 L, ((L - l : ℕ) : ℝ) * F l) - b * (L : ℝ) ^ 2 / 2| ≤
      (C + |b| / 2) * L * sqrt (L : ℝ) := by
  by_cases hL : L = 0
  · subst L
    simp
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hL
  have hroot : 1 ≤ sqrt (L : ℝ) := Real.one_le_sqrt.mpr hL1
  have hLsqrt : (L : ℝ) ≤ L * sqrt (L : ℝ) := by nlinarith
  have hbL : |b| * L / 2 ≤ (|b| / 2) * (L * sqrt (L : ℝ)) := by
    calc |b| * L / 2 = (|b| / 2) * L := by ring
      _ ≤ (|b| / 2) * (L * sqrt (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hLsqrt (by positivity)
  have hlin : ∀ N : ℕ, ∑ j ∈ range N, (j : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih => rw [sum_range_succ, ih]; push_cast; ring
  have hbound : |∑ j ∈ range L, ((∑ l ∈ Icc 1 j, F l) - b * j)| ≤ L * (C * sqrt (L : ℝ)) := by
    calc |∑ j ∈ range L, ((∑ l ∈ Icc 1 j, F l) - b * j)|
        ≤ ∑ j ∈ range L, |(∑ l ∈ Icc 1 j, F l) - b * j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range L, C * sqrt (L : ℝ) := by
          apply sum_le_sum
          intro j hj
          apply (h j).trans
          apply mul_le_mul_of_nonneg_left _ hC
          apply sqrt_le_sqrt
          exact_mod_cast (mem_range.mp hj).le
      _ = L * (C * sqrt (L : ℝ)) := by simp only [sum_const, card_range, nsmul_eq_mul]
  have heq : (∑ j ∈ range L, ∑ l ∈ Icc 1 j, F l) - b * (L : ℝ) ^ 2 / 2 =
      (∑ j ∈ range L, ((∑ l ∈ Icc 1 j, F l) - b * j)) - b * L / 2 := by
    rw [sum_sub_distrib, ← mul_sum, hlin]
    ring
  rw [weighted_prefix, heq]
  calc |(∑ j ∈ range L, ((∑ l ∈ Icc 1 j, F l) - b * j)) - b * L / 2|
      ≤ |∑ j ∈ range L, ((∑ l ∈ Icc 1 j, F l) - b * j)| + |b * L / 2|  := by
        simpa using abs_sub_le
          (∑ j ∈ range L, ((∑ l ∈ Icc 1 j, F l) - b * j)) 0 (b * L / 2)
    _ = |∑ j ∈ range L, ((∑ l ∈ Icc 1 j, F l) - b * j)| + |b| * L / 2 := by
        rw [abs_div, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (L : ℝ) by positivity)]
        norm_num
    _ ≤ L * (C * sqrt (L : ℝ)) + |b| * L / 2 := add_le_add hbound le_rfl
    _ ≤ L * (C * sqrt (L : ℝ)) + (|b| / 2) * (L * sqrt (L : ℝ)) := add_le_add le_rfl hbL
    _ = (C + |b| / 2) * L * sqrt (L : ℝ) := by ring

/-- The weighted Mersenne mean following HBP display 36. -/
theorem hbp_weighted_h_error (L : ℕ) :
    |(∑ l ∈ Icc 1 L, ((L - l : ℕ) : ℝ) * (h (2 ^ l - 1) : ℝ)) - C2 * (L : ℝ) ^ 2 / 2| ≤
      (16 * log 2 * exp 27 + |C2| / 2) * L * sqrt (L : ℝ) := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  exact prefix_error_to_weighted_error (fun l => (h (2 ^ l - 1) : ℝ)) C2
    (16 * log 2 * exp 27) (by positivity) hbp_h_mean_error L

/-- The normalized weighted mean has an explicit inverse square root error. -/
theorem hbp_weighted_h_normalized (L : ℕ) (hL : 1 ≤ L) :
    |(∑ l ∈ Icc 1 L, ((L - l : ℕ) : ℝ) * (h (2 ^ l - 1) : ℝ)) / (L : ℝ) ^ 2 - C2 / 2| ≤
      (16 * log 2 * exp 27 + |C2| / 2) / sqrt (L : ℝ) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hroot : 0 < sqrt (L : ℝ) := sqrt_pos.mpr hL0
  have heq :
      (∑ l ∈ Icc 1 L, ((L - l : ℕ) : ℝ) * (h (2 ^ l - 1) : ℝ)) / (L : ℝ) ^ 2 - C2 / 2 =
      ((∑ l ∈ Icc 1 L, ((L - l : ℕ) : ℝ) * (h (2 ^ l - 1) : ℝ)) - C2 * (L : ℝ) ^ 2 / 2) /
        (L : ℝ) ^ 2 := by field_simp
  rw [heq, abs_div, abs_of_nonneg (sq_nonneg (L : ℝ))]
  calc |(∑ l ∈ Icc 1 L, ((L - l : ℕ) : ℝ) * (h (2 ^ l - 1) : ℝ)) - C2 * (L : ℝ) ^ 2 / 2| /
        (L : ℝ) ^ 2
      ≤ ((16 * log 2 * exp 27 + |C2| / 2) * L * sqrt (L : ℝ)) / (L : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (hbp_weighted_h_error L) (by positivity)
    _ = (16 * log 2 * exp 27 + |C2| / 2) / sqrt (L : ℝ) := by
        field_simp
        nlinarith [Real.sq_sqrt hL0.le]

/-- The normalized weighted h mean tends to C2 divided by two. -/
theorem hbp_weighted_h_limit :
    Filter.Tendsto (fun L : ℕ =>
      (∑ l ∈ Icc 1 L, ((L - l : ℕ) : ℝ) * (h (2 ^ l - 1) : ℝ)) / (L : ℝ) ^ 2)
      Filter.atTop (nhds (C2 / 2)) := by
  have hs : Filter.Tendsto
      (fun L : ℕ => (16 * log 2 * exp 27 + |C2| / 2) / sqrt (L : ℝ))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hs.eventually (gt_mem_nhds hε), Filter.eventually_ge_atTop 1] with L hsmall hL
  rw [Real.dist_eq]
  exact (hbp_weighted_h_normalized L hL).trans_lt hsmall

end LeanLab.Romanov
