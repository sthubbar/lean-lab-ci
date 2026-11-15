import Mathlib

/-!
The vertical contour segment needs only absolute convergence in real part 2.
Trudgian arXiv:1206.1844v4 page 4, the paragraph before display 2.7.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.DERZ1997.Decomp576d
open Complex Filter Topology MeasureTheory Set

/-- Absolute convergence puts every character value on real part 2 near one.
Trudgian page 4, the Euler-series estimate for C2, derived with the Basel sum.
-/
theorem LFunction_near_one576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 2) :
    ‖DirichletCharacter.LFunction χ s - 1‖ ≤ 2 / 3 := by
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  have hf : Summable (LSeries.term (χ ·) s) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs1
  have hsplit := hf.sum_add_tsum_nat_add 2
  have hfirst : ∑ n ∈ Finset.range 2, LSeries.term (χ ·) s n = 1 := by
    simp [Finset.sum_range_succ, LSeries.term_of_ne_zero]
  rw [hfirst] at hsplit
  have htail : DirichletCharacter.LFunction χ s - 1 =
      ∑' n : ℕ, LSeries.term (χ ·) s (n + 2) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
    change (∑' n, LSeries.term (χ ·) s n) - 1 = _
    rw [← hsplit]
    ring
  have hbase := hasSum_zeta_two.summable
  have hbsplit := hbase.sum_add_tsum_nat_add 2
  have hbf : ∑ n ∈ Finset.range 2, (1 : ℝ) / (n : ℝ) ^ 2 = 1 := by norm_num [Finset.sum_range_succ]
  rw [hbf, hasSum_zeta_two.tsum_eq] at hbsplit
  have hmajor : ∀ n : ℕ, ‖LSeries.term (χ ·) s (n + 2)‖ ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
    intro n
    rw [LSeries.norm_term_eq]
    simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, hs,
      Real.rpow_two]
    apply div_le_div_of_nonneg_right
    · exact DirichletCharacter.norm_le_one χ _
    · positivity
  have htailbound : ‖DirichletCharacter.LFunction χ s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    rw [htail]
    calc
      _ ≤ ∑' n : ℕ, ‖LSeries.term (χ ·) s (n + 2)‖ :=
        norm_tsum_le_tsum_norm ((summable_nat_add_iff 2).mpr hf).norm
      _ ≤ ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 :=
        Summable.tsum_le_tsum hmajor ((summable_nat_add_iff 2).mpr hf).norm
          ((summable_nat_add_iff 2).mpr hbase)
      _ = _ := by linarith [hbsplit]
  have hpi : Real.pi ^ 2 ≤ 10 := by
    have hp := Real.pi_lt_d2
    have hp0 := Real.pi_pos
    nlinarith
  linarith

/-- The radius two thirds disc around one lies in the argument cone of width pi over two.
Trudgian page 4, auxiliary branch control for the C2 logarithm.
-/
theorem near_one_arg576 {z : ℂ} (hz : ‖z - 1‖ ≤ 2 / 3) :
    0 < z.re ∧ |Complex.arg z| ≤ Real.pi / 4 := by
  have hsq : (z.re - 1) ^ 2 + z.im ^ 2 ≤ 4 / 9 := by
    have hnorm : ‖z - 1‖ ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by nlinarith [norm_nonneg (z - 1)]
    have hh := hnorm
    rw [Complex.sq_norm, Complex.normSq_apply] at hh
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at hh
    nlinarith
  have hre : 0 < z.re := by nlinarith [sq_nonneg z.im]
  have him : |z.im| ≤ z.re := by
    have hsqim : z.im ^ 2 ≤ z.re ^ 2 := by
      nlinarith [sq_nonneg (z.re - 1 / 2)]
    apply (sq_le_sq₀ (abs_nonneg z.im) hre.le).mp
    simpa only [sq_abs] using hsqim
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have heq : Complex.arg z = Real.arctan (z.im / z.re) :=
    (Real.arctan_eq_of_tan_eq (Complex.tan_arg z) (abs_lt.mp ha)).symm
  refine ⟨hre, ?_⟩
  rw [heq, abs_le]
  have hratio : -1 ≤ z.im / z.re ∧ z.im / z.re ≤ 1 := by
    rw [le_div_iff₀ hre, div_le_iff₀ hre]
    rcases abs_le.mp him with ⟨hlo, hhi⟩
    constructor <;> linarith
  constructor
  · have h := Real.arctan_strictMono.monotone hratio.1
    simpa using h
  · have h := Real.arctan_strictMono.monotone hratio.2
    simpa using h

/-- The principal logarithm is a valid primitive along the vertical line at 2.
Trudgian page 4, the C2 estimate. Absolute convergence keeps the image in the
right half-plane, so no discontinuous branch is integrated.
-/
theorem vertical_log_integral576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    I * (∫ t in (-T)..T,
      logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I)) =
      Complex.log (DirichletCharacter.LFunction χ ((2 : ℂ) + (T : ℂ) * I)) -
      Complex.log (DirichletCharacter.LFunction χ ((2 : ℂ) - (T : ℂ) * I)) := by
  let L := DirichletCharacter.LFunction χ
  have hanalytic (t : ℝ) : AnalyticAt ℂ L ((2 : ℂ) + (t : ℂ) * I) := by
    have hd : DifferentiableOn ℂ L {s : ℂ | 1 < s.re} := by
      intro z hz
      exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl (by
        intro h
        rw [h] at hz
        norm_num at hz))).differentiableWithinAt
    exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))
  have hre (t : ℝ) : 0 < (L ((2 : ℂ) + (t : ℂ) * I)).re :=
    (near_one_arg576 (LFunction_near_one576 χ (by simp))).1
  have hne (t : ℝ) : L ((2 : ℂ) + (t : ℂ) * I) ≠ 0 :=
    ne_zero_of_re_pos (hre t)
  have hc : Continuous (fun t : ℝ => logDeriv L ((2 : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hlog : ContinuousAt (logDeriv L) ((2 : ℂ) + (t : ℂ) * I) := by
      exact (hanalytic t).deriv.continuousAt.div (hanalytic t).continuousAt (hne t)
    have hline : ContinuousAt (fun u : ℝ => (2 : ℂ) + (u : ℂ) * I) t := by fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => (2 : ℂ) + (u : ℂ) * I) hlog hline
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Complex.log (L ((2 : ℂ) + (t : ℂ) * I)))
      (I * logDeriv L ((2 : ℂ) + (t : ℂ) * I)) t := by
    have hline : HasDerivAt (fun u : ℂ => (2 : ℂ) + u * I) I (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add 2
    have hL := ((hanalytic t).differentiableAt.hasDerivAt).comp (t : ℂ) hline
    have hh := ((Complex.hasDerivAt_log (Or.inl (hre t))).comp (t : ℂ) hL).comp_ofReal
    convert hh using 1
    · rfl
    · simp only [logDeriv_apply]
      ring
  have hi : IntervalIntegrable (fun t : ℝ => I * logDeriv L ((2 : ℂ) + (t : ℂ) * I))
      volume (-T) T := (continuous_const.mul hc).intervalIntegrable _ _
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at hh
  simpa only [L, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using hh

/-- The vertical signed argument divided by pi is at most one half at every height.
Trudgian page 4, the C2 estimate, with a derived loose constant from the near-one disc.
-/
theorem vertical_half_bound576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    |(I * (∫ t in (-T)..T,
      logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + (t : ℂ) * I))).im /
        Real.pi| ≤ 1 / 2 := by
  rw [vertical_log_integral576]
  simp only [Complex.sub_im, Complex.log_im, abs_div, abs_of_pos Real.pi_pos]
  rw [div_le_iff₀ Real.pi_pos]
  have hp := (near_one_arg576 (LFunction_near_one576 χ (s := (2 : ℂ) + (T : ℂ) * I)
    (by simp))).2
  have hm := (near_one_arg576 (LFunction_near_one576 χ (s := (2 : ℂ) - (T : ℂ) * I)
    (by simp))).2
  have htri := abs_sub_le
    (Complex.arg (DirichletCharacter.LFunction χ ((2 : ℂ) + (T : ℂ) * I))) (0 : ℝ)
    (Complex.arg (DirichletCharacter.LFunction χ ((2 : ℂ) - (T : ℂ) * I)))
  simp only [sub_zero, zero_sub, abs_neg] at htri
  linarith

end LeanLab.DERZ1997.Decomp576d
