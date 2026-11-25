import Mathlib

/-!
Certified upper bounds for the two logarithmic integrals F7 and F8 of Wu 2004 Section 10,
equations 10.10 and 10.11, https://arxiv.org/pdf/0705.1652, page 41, whose printed values
appear in the final display on page 42 as 0.004609 and 0.434368.
After the shift s = t - 2 the integrand is log of 1 + s over 2 + s on an interval inside
the unit disc. The logarithm is bounded above by its Taylor polynomial plus the Mathlib
remainder bound, and the reciprocal of 2 + s by a geometric partial sum of odd length.
The product polynomial is integrated exactly and compared with the printed value.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ChenDoubleSieve.Feed1122LogInt

open Real Finset MeasureTheory intervalIntegral

/-- Taylor coefficient of the logarithm. -/
noncomputable def la (i : ℕ) : ℝ := (-1) ^ i / ((i : ℝ) + 1)

/-- Geometric coefficient of the reciprocal of 2 + s. -/
noncomputable def rb (j : ℕ) : ℝ := (-1) ^ j / 2 ^ (j + 1)

/-- Pointwise upper bound for log of 1 + s on the interval from 0 to x0. -/
theorem log_le_poly (x0 s : ℝ) (hx1 : x0 < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ x0) (n : ℕ) :
    log (1 + s) ≤ (∑ i ∈ range n, la i * s ^ (i + 1)) + 1 / (1 - x0) * s ^ (n + 1) := by
  have hs : |(-s)| < 1 := by rw [abs_neg, abs_of_nonneg hs0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hs n
  rw [abs_neg, abs_of_nonneg hs0, sub_neg_eq_add] at h
  have h2 := (abs_le.mp h).1
  have hsum : (∑ i ∈ range n, (-s) ^ (i + 1) / ((i : ℝ) + 1)) =
      -∑ i ∈ range n, la i * s ^ (i + 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [la, neg_pow s, pow_succ]
    ring
  have hrem : s ^ (n + 1) / (1 - s) ≤ 1 / (1 - x0) * s ^ (n + 1) := by
    rw [div_eq_mul_one_div, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hs0 _)
    apply one_div_le_one_div_of_le <;> linarith
  rw [hsum] at h
  have h3 := (abs_le.mp h).2
  linarith

/-- Pointwise upper bound for the reciprocal of 2 + s, for an odd number of terms. -/
theorem inv_le_poly (s : ℝ) (hs0 : 0 ≤ s) (k : ℕ) (hk : Odd k) :
    1 / (2 + s) ≤ ∑ j ∈ range k, rb j * s ^ j := by
  have hgeom : (2 + s) * (∑ j ∈ range k, rb j * s ^ j) = 1 - (-s / 2) ^ k := by
    have : (∑ j ∈ range k, rb j * s ^ j) = (1 / 2) * ∑ j ∈ range k, (-s / 2) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [rb, div_pow, neg_pow s, pow_succ]
      field_simp
    rw [this]
    have h := geom_sum_mul (-s / 2) k
    have h' : (2 + s) * (1 / 2 * ∑ j ∈ range k, (-s / 2) ^ j) =
        -((∑ i ∈ range k, (-s / 2) ^ i) * (-s / 2 - 1)) := by ring
    rw [h', h]
    ring
  have hodd : (-s / 2) ^ k ≤ 0 := by
    rw [neg_div, hk.neg_pow]
    exact neg_nonpos.mpr (pow_nonneg (by linarith) _)
  have hpos : (0 : ℝ) < 2 + s := by linarith
  rw [div_le_iff₀ hpos, mul_comm, hgeom]
  linarith

/-- The polynomial majorant, expanded into monomials. -/
noncomputable def majorant (x0 : ℝ) (n k : ℕ) (s : ℝ) : ℝ :=
  (∑ i ∈ range n, ∑ j ∈ range k, la i * rb j * s ^ (i + j + 1)) +
    ∑ j ∈ range k, 1 / (1 - x0) * rb j * s ^ (n + j + 1)

theorem majorant_eq (x0 : ℝ) (n k : ℕ) (s : ℝ) :
    majorant x0 n k s = ((∑ i ∈ range n, la i * s ^ (i + 1)) + 1 / (1 - x0) * s ^ (n + 1)) *
      ∑ j ∈ range k, rb j * s ^ j := by
  rw [majorant, add_mul, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    ring

/-- Exact integral of the majorant. -/
theorem integral_majorant (x0 : ℝ) (n k : ℕ) :
    ∫ s in (0 : ℝ)..x0, majorant x0 n k s =
      (∑ i ∈ range n, ∑ j ∈ range k,
          la i * rb j * (x0 ^ (i + j + 1 + 1) / (((i + j + 1 : ℕ) : ℝ) + 1))) +
        ∑ j ∈ range k, 1 / (1 - x0) * rb j *
          (x0 ^ (n + j + 1 + 1) / (((n + j + 1 : ℕ) : ℝ) + 1)) := by
  unfold majorant
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_finsetSum, intervalIntegral.integral_finsetSum]
    · congr 1
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [intervalIntegral.integral_finsetSum]
        · refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [intervalIntegral.integral_const_mul, integral_pow]
          simp
        · intro j _
          exact (by fun_prop : Continuous fun s : ℝ => la i * rb j * s ^ (i + j + 1)).intervalIntegrable _ _
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp
    · intro j _
      exact (by fun_prop : Continuous fun s : ℝ => 1 / (1 - x0) * rb j * s ^ (n + j + 1)).intervalIntegrable _ _
    · intro i _
      exact (by fun_prop : Continuous fun s : ℝ =>
        ∑ j ∈ range k, la i * rb j * s ^ (i + j + 1)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun s : ℝ =>
      ∑ i ∈ range n, ∑ j ∈ range k, la i * rb j * s ^ (i + j + 1)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun s : ℝ =>
      ∑ j ∈ range k, 1 / (1 - x0) * rb j * s ^ (n + j + 1)).intervalIntegrable _ _

/-- The shifted log integral is at most the integral of the majorant. -/
theorem logint_le_majorant (x0 : ℝ) (hx0 : 0 ≤ x0) (hx1 : x0 < 1) (n k : ℕ) (hk : Odd k) :
    ∫ t in (2 : ℝ)..(2 + x0), log (t - 1) / t ≤ ∫ s in (0 : ℝ)..x0, majorant x0 n k s := by
  have hshift : ∫ t in (2 : ℝ)..(2 + x0), log (t - 1) / t =
      ∫ s in (0 : ℝ)..x0, log (1 + s) / (2 + s) := by
    have h := intervalIntegral.integral_comp_add_right (fun t : ℝ => log (t - 1) / t)
      (a := (0 : ℝ)) (b := x0) 2
    simp only [zero_add] at h
    rw [add_comm (2 : ℝ) x0, ← h]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    ring_nf
  rw [hshift]
  refine intervalIntegral.integral_mono_on hx0 ?_ ?_ ?_
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx0]
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro s hs
      linarith [hs.1]
    · fun_prop
    · intro s hs
      linarith [hs.1]
  · exact (by unfold majorant; fun_prop : Continuous (majorant x0 n k)).intervalIntegrable _ _
  · intro s hs
    rw [majorant_eq]
    have hL := log_le_poly x0 s hx1 hs.1 hs.2 n
    have hR := inv_le_poly s hs.1 k hk
    have hlog : 0 ≤ log (1 + s) := Real.log_nonneg (by linarith [hs.1])
    have hRpos : 0 ≤ 1 / (2 + s) := by
      apply div_nonneg zero_le_one; linarith [hs.1]
    calc log (1 + s) / (2 + s) = log (1 + s) * (1 / (2 + s)) := by ring
      _ ≤ log (1 + s) * ∑ j ∈ range k, rb j * s ^ j := mul_le_mul_of_nonneg_left hR hlog
      _ ≤ _ := mul_le_mul_of_nonneg_right hL (le_trans hRpos hR)

/-- Wu 2004 page 41 equation 10.10 and page 42 final display: the value of F7 is at most
0.004609. Here 84/41 is 1/sigma1 - 1 for sigma1 = 41/125. -/
theorem logint_F7 :
    8 * ∫ t in (2 : ℝ)..(84 / 41 : ℝ), Real.log (t - 1) / t ≤ 0.004609 := by
  have h := logint_le_majorant (2 / 41) (by norm_num) (by norm_num) 5 5 (by decide)
  rw [integral_majorant] at h
  have he : (84 / 41 : ℝ) = 2 + 2 / 41 := by norm_num
  rw [he]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, la, rb] at h
  norm_num at h ⊢
  linarith

/-- Wu 2004 page 41 equation 10.11 and page 42 final display: the value of F8 is at most
0.434368. Here 359/141 is 1/sigma2 - 1 for sigma2 = 141/500. -/
theorem logint_F8 :
    8 * ∫ t in (2 : ℝ)..(359 / 141 : ℝ), Real.log (t - 1) / t ≤ 0.434368 := by
  have h := logint_le_majorant (77 / 141) (by norm_num) (by norm_num) 24 13 (by decide)
  rw [integral_majorant] at h
  have he : (359 / 141 : ℝ) = 2 + 77 / 141 := by norm_num
  rw [he]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, la, rb] at h
  norm_num at h ⊢
  linarith

end LeanLab.ChenDoubleSieve.Feed1122LogInt
