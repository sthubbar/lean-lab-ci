/-
Jia 1996 pages 283 and 285, numerical integrals in displays 60 and 64.
Source https://doi.org/10.4064/aa-77-3-207-287.
Certified polynomial enclosures for the printed numerical coefficients.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Languasco2004.LogApprox565
open Finset Real intervalIntegral
noncomputable section
set_option maxHeartbeats 0

/-- Pages 283 and 285: a polynomial approximation to log on the interval one to two. -/
def logPoly (y : ℝ) : ℝ :=
  0.4054651081 - ∑ i ∈ range 20, (1 - 2 * y / 3) ^ (i + 1) / (i + 1)

/-- Pages 283 and 285: certify the constant at the centre of the logarithm expansion. -/
theorem log_three_halves_bounds :
    (0.4054651081 : ℝ) ≤ log (3 / 2) ∧ log (3 / 2) ≤ 0.4054651082 := by
  have hl := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 5)
    (by norm_num : (1 / 5 : ℝ) < 1) 10
  have hu := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1 / 5)
    (by norm_num : (1 / 5 : ℝ) < 1) 10
  norm_num [sum_range_succ] at hl hu
  constructor <;> linarith

/-- Pages 283 and 285: the logarithm approximation has a uniform certified error. -/
theorem logPoly_error (y : ℝ) (hy : 1 ≤ y) (hy2 : y ≤ 2) :
    |log y - logPoly y| ≤ 0.000000001 := by
  let x := 1 - 2 * y / 3
  have hx : |x| ≤ (1 / 3 : ℝ) := by
    apply abs_le.mpr
    dsimp [x]
    constructor <;> linarith
  have hx1 : |x| < 1 := hx.trans_lt (by norm_num)
  have h := Real.abs_log_sub_add_sum_range_le hx1 20
  have hp : |x| ^ 21 ≤ (1 / 3 : ℝ) ^ 21 := pow_le_pow_left₀ (abs_nonneg _) hx _
  have hd : (2 / 3 : ℝ) ≤ 1 - |x| := by linarith
  have he : |x| ^ 21 / (1 - |x|) ≤ (1 / 3 : ℝ) ^ 21 / (2 / 3) :=
    div_le_div₀ (by positivity) hp (by norm_num) hd
  have hl : log (1 - x) = log y - log (3 / 2) := by
    dsimp [x]
    rw [show (1 - (1 - 2 * y / 3)) = y / (3 / 2) by ring]
    exact log_div (by linarith) (by norm_num)
  rw [hl] at h
  have hmain : |log y - logPoly y - (log (3 / 2) - 0.4054651081)| ≤
      (1 / 3 : ℝ) ^ 21 / (2 / 3) := by
    convert h.trans he using 1 <;> simp only [logPoly, x] <;> congr 1 <;> ring
  have hc := log_three_halves_bounds
  have hcl : |log (3 / 2) - (0.4054651081 : ℝ)| ≤ 0.0000000001 :=
    abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have htri := abs_add_le (log y - logPoly y - (log (3 / 2) - 0.4054651081))
    (log (3 / 2) - 0.4054651081)
  have hsum : |log y - logPoly y| ≤
      |log y - logPoly y - (log (3 / 2) - 0.4054651081)| +
      |log (3 / 2) - 0.4054651081| := by convert htri using 1 <;> ring
  exact hsum.trans ((add_le_add hmain hcl).trans (by norm_num))

/-- Pages 283 and 285: a finite geometric reciprocal approximation. -/
def recipPoly (c t : ℝ) : ℝ := (∑ i ∈ range 24, (1 - t / c) ^ i) / c

/-- Pages 283 and 285: the reciprocal error is bounded uniformly on each source interval. -/
theorem recipPoly_error (c t : ℝ) (hc : 0 < c) (ht : 1 / 10 ≤ t)
    (htc : 3 / 5 * c ≤ t) (htC : t ≤ c) :
    |1 / t - recipPoly c t| ≤ 0.000000003 ∧ |recipPoly c t| ≤ 10 := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 ≤ 1 - t / c := by exact sub_nonneg.mpr ((div_le_one hc).mpr htC)
  have hx : 1 - t / c ≤ (2 / 5 : ℝ) := by
    have h := (le_div_iff₀ hc).mpr htc
    linarith
  have he : recipPoly c t * t = 1 - (1 - t / c)^24 := by
    have hgeom := geom_sum_mul (1 - t / c) 24
    unfold recipPoly
    field_simp at hgeom ⊢
    nlinarith [hgeom]
  have hp : (1 - t / c)^24 ≤ (2 / 5 : ℝ)^24 := pow_le_pow_left₀ hx0 hx _
  have hR0 : 0 ≤ recipPoly c t := by unfold recipPoly; positivity
  have hR : recipPoly c t ≤ 1 / t := by
    apply (le_div_iff₀ ht0).mpr
    nlinarith [pow_nonneg hx0 24]
  have hi : 1 / t ≤ (10 : ℝ) := (div_le_iff₀ ht0).mpr (by linarith)
  constructor
  · rw [abs_of_nonneg (sub_nonneg.mpr hR)]
    apply (mul_le_mul_iff_left₀ ht0).mp
    rw [sub_mul, one_div_mul_cancel ht0.ne', he]
    have : (2 / 5 : ℝ)^24 ≤ 0.000000003 * (1 / 10) := by norm_num
    nlinarith
  · rw [abs_of_nonneg hR0]
    exact hR.trans hi

/-- Pages 283 and 285: squaring the log approximation preserves a small uniform error. -/
theorem logPoly_sq_error (y : ℝ) (hy : 1 ≤ y) (hy2 : y ≤ 2) :
    |log y ^ 2 - logPoly y ^ 2| ≤ 0.000000003 := by
  have he := logPoly_error y hy hy2
  have hl : 0 ≤ log y := log_nonneg hy
  have hu : log y ≤ 1 := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hp := abs_le.mp he
  have hs : |log y + logPoly y| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc |log y ^ 2 - logPoly y ^ 2| = |log y - logPoly y| * |log y + logPoly y| := by
         rw [← abs_mul]; congr 1; ring
       _ ≤ 0.000000001 * 3 := mul_le_mul he hs (abs_nonneg _) (by norm_num)
       _ = 0.000000003 := by norm_num

/-- Pages 283 and 285: certify the product needed by the main integral. -/
theorem log_recip_error (c t y : ℝ) (hc : 0 < c) (ht : 1 / 10 ≤ t)
    (htc : 3 / 5 * c ≤ t) (htC : t ≤ c) (hy : 1 ≤ y) (hy2 : y ≤ 2) :
    |log y / t - logPoly y * recipPoly c t| ≤ 0.00000002 := by
  obtain ⟨hR, hRb⟩ := recipPoly_error c t hc ht htc htC
  have hL := logPoly_error y hy hy2
  have hLb : |log y| ≤ 1 := by
    rw [abs_of_nonneg (log_nonneg hy)]
    exact (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h := abs_add_le (log y * (1 / t - recipPoly c t))
    ((log y - logPoly y) * recipPoly c t)
  have he : log y / t - logPoly y * recipPoly c t =
      log y * (1 / t - recipPoly c t) + (log y - logPoly y) * recipPoly c t := by ring
  rw [he]
  calc _ ≤ |log y| * |1 / t - recipPoly c t| +
      |log y - logPoly y| * |recipPoly c t| := by simpa only [abs_mul] using h
       _ ≤ 1 * 0.000000003 + 0.000000001 * 10 :=
         add_le_add (mul_le_mul hLb hR (abs_nonneg _) (by norm_num))
           (mul_le_mul hL hRb (abs_nonneg _) (by norm_num))
       _ ≤ 0.00000002 := by norm_num

/-- Pages 283 and 285: certify the product needed by the triple integrals. -/
theorem logsq_recip_error (c t y : ℝ) (hc : 0 < c) (ht : 1 / 10 ≤ t)
    (htc : 3 / 5 * c ≤ t) (htC : t ≤ c) (hy : 1 ≤ y) (hy2 : y ≤ 2) :
    |log y ^ 2 / t - logPoly y ^ 2 * recipPoly c t| ≤ 0.00000004 := by
  obtain ⟨hR, hRb⟩ := recipPoly_error c t hc ht htc htC
  have hL := logPoly_sq_error y hy hy2
  have hl : 0 ≤ log y := log_nonneg hy
  have hu : log y ≤ 1 := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hLb : |log y ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have h := abs_add_le (log y ^ 2 * (1 / t - recipPoly c t))
    ((log y ^ 2 - logPoly y ^ 2) * recipPoly c t)
  have he : log y ^ 2 / t - logPoly y ^ 2 * recipPoly c t =
      log y ^ 2 * (1 / t - recipPoly c t) +
        (log y ^ 2 - logPoly y ^ 2) * recipPoly c t := by ring
  rw [he]
  calc _ ≤ |log y ^ 2| * |1 / t - recipPoly c t| +
      |log y ^ 2 - logPoly y ^ 2| * |recipPoly c t| := by simpa only [abs_mul] using h
       _ ≤ 1 * 0.000000003 + 0.000000003 * 10 :=
         add_le_add (mul_le_mul hLb hR (abs_nonneg _) (by norm_num))
           (mul_le_mul hL hRb (abs_nonneg _) (by norm_num))
       _ ≤ 0.00000004 := by norm_num

/-- Pages 283 and 285: integrate the certified log reciprocal error over a source interval. -/
theorem integral_log_approx (a b A B : ℝ) (hab : a ≤ b) (ha : 1 / 10 ≤ a)
    (hab' : 3 / 5 * b ≤ a) (hb : 0 < b)
    (hy : ∀ t ∈ Set.Icc a b, 1 ≤ A + B * t ∧ A + B * t ≤ 2) :
    |(∫ t in a..b, log (A + B * t) / t) -
      ∫ t in a..b, logPoly (A + B * t) * recipPoly b t| ≤ 0.00000002 * (b - a) := by
  have hF : IntervalIntegrable (fun t => log (A + B * t) / t) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · fun_prop
      · intro t ht
        have := (hy t ht).1
        linarith
    · fun_prop
    · intro t ht
      linarith [ht.1]
  have hP : IntervalIntegrable (fun t => logPoly (A + B * t) * recipPoly b t)
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    unfold logPoly recipPoly
    fun_prop
  rw [← integral_sub hF hP]
  have h := norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun t => log (A + B * t) / t - logPoly (A + B * t) * recipPoly b t)
    (C := 0.00000002) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht' : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, ht.2⟩
      rw [Real.norm_eq_abs]
      exact log_recip_error b t (A + B * t) hb (ha.trans ht'.1)
        (hab'.trans ht'.1) ht'.2 (hy t ht').1 (hy t ht').2)
  simpa only [Real.norm_eq_abs, Set.uIoc_of_le hab, abs_of_nonneg (sub_nonneg.mpr hab)] using h

/-- Pages 283 and 285: integrate the squared log reciprocal error. -/
theorem integral_logsq_approx (a b A B : ℝ) (hab : a ≤ b) (ha : 1 / 10 ≤ a)
    (hab' : 3 / 5 * b ≤ a) (hb : 0 < b)
    (hy : ∀ t ∈ Set.Icc a b, 1 ≤ A + B * t ∧ A + B * t ≤ 2) :
    |(∫ t in a..b, log (A + B * t)^2 / t) -
      ∫ t in a..b, logPoly (A + B * t)^2 * recipPoly b t| ≤ 0.00000004 * (b - a) := by
  have hF : IntervalIntegrable (fun t => log (A + B * t)^2 / t) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div
    · apply ContinuousOn.pow
      apply ContinuousOn.log
      · fun_prop
      · intro t ht
        have := (hy t ht).1
        linarith
    · fun_prop
    · intro t ht
      linarith [ht.1]
  have hP : IntervalIntegrable (fun t => logPoly (A + B * t)^2 * recipPoly b t)
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    unfold logPoly recipPoly
    fun_prop
  rw [← integral_sub hF hP]
  have h := norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun t => log (A + B * t)^2 / t - logPoly (A + B * t)^2 * recipPoly b t)
    (C := 0.00000004) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht' : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, ht.2⟩
      rw [Real.norm_eq_abs]
      exact logsq_recip_error b t (A + B * t) hb (ha.trans ht'.1)
        (hab'.trans ht'.1) ht'.2 (hy t ht').1 (hy t ht').2)
  simpa only [Real.norm_eq_abs, Set.uIoc_of_le hab, abs_of_nonneg (sub_nonneg.mpr hab)] using h

#print axioms integral_log_approx
#print axioms integral_logsq_approx
#print axioms log_three_halves_bounds
#print axioms logPoly_error
#print axioms recipPoly_error
#print axioms logPoly_sq_error
#print axioms log_recip_error
#print axioms logsq_recip_error
end
end LeanLab.Languasco2004.LogApprox565
