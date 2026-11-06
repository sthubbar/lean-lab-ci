import LeanLab.GoldbachAverage.PowerIntegral444

/-!
Finite square expansion for the pair integration on BHMS pages 18 and 19.
Source: https://arxiv.org/abs/1704.06103v2.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.FinitePower444
open MeasureTheory Complex Finset Set

/-- BHMS pages 18 and 19, the integral of a finite square is bounded by its integrated pair norms. -/
theorem square_integral_le_pairs {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ i ∈ S, ContinuousOn (f i) (Icc a b)) :
    (∫ u in a..b, ‖∑ i ∈ S, f i u‖ ^ 2) ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖∫ u in a..b, f i u * star (f j u)‖ := by
  classical
  have hfull (u : ℝ) : ‖∑ i ∈ S, f i u‖ ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, (f i u * star (f j u)).re := by
    rw [Complex.sq_norm]
    have h := congrArg Complex.re (Complex.mul_conj (∑ i ∈ S, f i u))
    simp only [Complex.ofReal_re] at h
    rw [← h]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    rfl
  have hp (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      IntervalIntegrable (fun u => f i u * star (f j u)) volume a b :=
    ((hf i hi).mul (hf j hj).star).intervalIntegrable_of_Icc hab
  have hpr (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      IntervalIntegrable (fun u => (f i u * star (f j u)).re) volume a b :=
    (Complex.continuous_re.comp_continuousOn ((hf i hi).mul (hf j hj).star)).intervalIntegrable_of_Icc hab
  calc _ = ∫ u in a..b, ∑ i ∈ S, ∑ j ∈ S, (f i u * star (f j u)).re := by
        apply intervalIntegral.integral_congr
        intro u _
        exact hfull u
    _ = ∑ i ∈ S, ∑ j ∈ S, (∫ u in a..b, f i u * star (f j u)).re := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [intervalIntegral.integral_finsetSum (fun j hj => hpr i hi j hj)]
        apply Finset.sum_congr rfl
        intro j hj
        exact Complex.reCLM.intervalIntegral_comp_comm (hp i hi j hj)
      · intro i hi
        convert IntervalIntegrable.sum S (fun j hj => hpr i hi j hj) using 1
        funext u
        simp
    _ ≤ _ := Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => Complex.re_le_norm _

/-- BHMS pages 18 and 19, one weighted power pair contributes a reciprocal separation kernel. -/
theorem power_pair_integral_bound (c d e f : ℂ) (he : e.re ≤ 1) (hf : f.re ≤ 1)
    (x : ℝ) (hx : 0 < x) :
    ‖∫ u in x..(3 * x), (c * (u : ℂ) ^ e) * star (d * (u : ℂ) ^ f)‖ ≤
      56 * ‖c‖ * ‖d‖ * x ^ (e.re + f.re + 1) / (1 + |e.im - f.im|) := by
  have hform (u : ℝ) (hu : u ∈ Set.uIcc x (3 * x)) :
      (c * (u : ℂ) ^ e) * star (d * (u : ℂ) ^ f) =
        (c * star d) * (u : ℂ) ^ (e + star f) := by
    rw [Set.uIcc_of_le (by linarith : x ≤ 3 * x)] at hu
    have hu0 : 0 < u := lt_of_lt_of_le hx hu.1
    have hc : star ((u : ℂ) ^ f) = (u : ℂ) ^ star f := by
      have hc := Complex.cpow_conj (u : ℂ) f (by
        rw [Complex.arg_ofReal_of_nonneg hu0.le]
        exact Real.pi_ne_zero.symm)
      change star ((u : ℂ) ^ f) = (u : ℂ) ^ (starRingEnd ℂ) f
      rw [Complex.conj_ofReal] at hc
      exact hc.symm
    rw [star_mul, hc, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu0.ne')]
    ring
  rw [intervalIntegral.integral_congr hform, intervalIntegral.integral_const_mul,
    norm_mul, norm_mul, norm_star]
  have hb := PowerIntegral444.power_integral_bound (e + star f) (by
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
    linarith) x hx
  have hb' := mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg c) (norm_nonneg d))
  simp only [Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, ← sub_eq_add_neg] at hb'
  simp only [starRingEnd_apply] at hb'
  convert hb' using 1 <;> ring

/-- BHMS pages 18 and 19, the finite weighted power square is bounded by its pair kernel sum. -/
theorem finite_power_energy {ι : Type*} (S : Finset ι) (c e : ι → ℂ)
    (he : ∀ i ∈ S, (e i).re ≤ 1) (x : ℝ) (hx : 0 < x) :
    (∫ u in x..(3 * x), ‖∑ i ∈ S, c i * (u : ℂ) ^ e i‖ ^ 2) ≤
      ∑ i ∈ S, ∑ j ∈ S,
        56 * ‖c i‖ * ‖c j‖ * x ^ ((e i).re + (e j).re + 1) /
          (1 + |(e i).im - (e j).im|) := by
  have hc (i : ι) : ContinuousOn (fun u : ℝ => c i * (u : ℂ) ^ e i) (Icc x (3 * x)) := by
    intro u hu
    exact ((Complex.continuousAt_ofReal_cpow_const u (e i)
      (Or.inr (ne_of_gt (lt_of_lt_of_le hx hu.1)))).const_mul (c i)).continuousWithinAt
  refine (square_integral_le_pairs S (fun i u => c i * (u : ℂ) ^ e i) x (3 * x)
    (by linarith) (fun i _ => hc i)).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact power_pair_integral_bound (c i) (c j) (e i) (e j) (he i hi) (he j hj) x hx

/-- BHMS page 19 reciprocal product comparison, with an explicit symmetric square bound. -/
theorem reciprocal_pair (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (a * b) ≤ 1 / a ^ 2 + 1 / b ^ 2 := by
  apply (div_le_iff₀ (mul_pos ha hb)).mpr
  have hab : a ≠ 0 := ha.ne'
  have hbb : b ≠ 0 := hb.ne'
  field_simp
  nlinarith [sq_nonneg (a - b)]

end LeanLab.GoldbachAverage.FinitePower444
