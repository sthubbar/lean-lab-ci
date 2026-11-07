import LeanLab.GoldbachAverage.Decomp287d
import LeanLab.GoldbachAverage.PairKernel402

/-!
BHMS, arXiv 1704.06103v2 page 18, low zero part of Lemma 7.
The integrated pair kernel and the ordinate pair count are separate leaves.
Every pair weight uses the actual zero multiplicities.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp402c
open MeasureTheory
open Decomp287d

/-- The low ordinate pair kernel on BHMS page 18 after expansion of the square.
Both zero ranges retain the cutoff x over h. -/
def lowPairWeight (x h : ℝ) : ℝ :=
  ∑' ρ : NontrivialZero, ∑' σ : NontrivialZero,
    if |ρ.1.im| ≤ x / h ∧ |σ.1.im| ≤ x / h then
      (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
        (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|)
    else 0

/-- The pair weight is nonnegative, as in the BHMS page 18 positive kernel display. -/
theorem lowPairWeight_nonneg (x h : ℝ) : 0 ≤ lowPairWeight x h := by
  apply tsum_nonneg
  intro ρ
  apply tsum_nonneg
  intro σ
  split_ifs <;> positivity

/-! ## Auxiliary lemmas: interval Cauchy-Schwarz, the sliding-window change of order,
and the oscillatory power pair integrals.

These are private copies of Mathlib-only results that already exist elsewhere in
`GoldbachAverage` (`WindowCauchy444`, `Sliding124`, `PowerIntegral444`,
`FinitePower444`).  Those modules cannot be imported here: each of them (and the
assembled low zero variance files) imports this one, so an import would be a cycle. -/

section

open Set Filter ContinuousLinearMap
open scoped Convolution

/-- The complex interval integral square costs the interval length (Holder, 2 and 2). -/
private theorem aux_norm_integral_square_le (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b))) :
    ‖∫ u in a..b, f u‖ ^ 2 ≤ (b - a) * ∫ u in a..b, ‖f u‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hg : MemLp (fun u => ‖f u‖) (ENNReal.ofReal 2) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hf.norm
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    exact MemLp.of_bound measurable_const.aestronglyMeasurable 1
      (Eventually.of_forall fun _ => by simp)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff])
    (Eventually.of_forall fun u => norm_nonneg (f u))
    (Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1)) hg hone
  norm_num only [Real.rpow_two, one_pow, mul_one] at hHolder
  have hOneInt : (∫ _u, (1 : ℝ) ∂μ) = b - a := by
    change (∫ _u in Set.Ioc a b, (1 : ℝ)) = b - a
    rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul,
      mul_one]
  rw [hOneInt, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hHolder
  have hcs : (∫ u in a..b, ‖f u‖) ≤
      Real.sqrt (∫ u in a..b, ‖f u‖ ^ 2) * Real.sqrt (b - a) := by
    simpa only [intervalIntegral.integral_of_le hab, μ] using hHolder
  have hI0 : 0 ≤ ∫ u in a..b, ‖f u‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) hab
  have hmain := pow_le_pow_left₀ (norm_nonneg _) (hn.trans hcs) 2
  rw [mul_pow, Real.sq_sqrt hI0, Real.sq_sqrt (sub_nonneg.mpr hab)] at hmain
  simpa only [mul_comm] using hmain

/-- A sliding interval integral is a convolution with the backward interval indicator. -/
private theorem aux_window_eq_convolution (f : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    (f ⋆ ((Ico (-h) 0).indicator (fun _ => (1 : ℝ)))) x = ∫ u in x..(x + h), f u := by
  classical
  rw [convolution_def]
  simp only [lsmul_apply, smul_eq_mul]
  have heq : (fun u : ℝ => f u * (Ico (-h) 0).indicator (fun _ => (1 : ℝ)) (x - u)) =
      (Ioc x (x + h)).indicator f := by
    funext u
    by_cases hu : u ∈ Ioc x (x + h)
    · have ht : x - u ∈ Ico (-h) 0 := by
        obtain ⟨h1, h2⟩ := hu
        constructor <;> linarith
      simp only [indicator_of_mem ht, indicator_of_mem hu, mul_one]
    · have ht : x - u ∉ Ico (-h) 0 := by
        intro ht
        apply hu
        obtain ⟨h1, h2⟩ := ht
        constructor <;> linarith
      simp only [indicator_of_notMem ht, indicator_of_notMem hu, mul_zero]
  rw [heq, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith)]

/-- The backward interval indicator has mass `h` for nonnegative `h`. -/
private theorem aux_backward_window_mass {h : ℝ} (hh : 0 ≤ h) :
    (∫ t : ℝ, (Ico (-h) 0).indicator (fun _ => (1 : ℝ)) t) = h := by
  rw [integral_indicator measurableSet_Ico]
  simp [measureReal_def, Real.volume_Ico, hh]

/-- The sliding window covers a point for starting positions of length at most `h`. -/
private theorem aux_sliding_integral_le {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ u : ℝ, 0 ≤ f u) {h : ℝ} (hh : 0 ≤ h) :
    (∫ x : ℝ in Ioi 0, ∫ u in x..(x + h), f u) ≤ h * ∫ u : ℝ, f u := by
  classical
  let k : ℝ → ℝ := (Ico (-h) 0).indicator (fun _ => (1 : ℝ))
  have hk : Integrable k := by
    rw [show k = (Ico (-h) 0).indicator (fun _ => (1 : ℝ)) from rfl,
      integrable_indicator_iff measurableSet_Ico]
    exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hk0 : ∀ t, 0 ≤ k t := by
    intro t
    by_cases ht : t ∈ Ico (-h) 0 <;> simp [k, ht]
  have hconv : Integrable (f ⋆ k) := hf.integrable_convolution (L := lsmul ℝ ℝ) hk
  have hconv0 : ∀ x : ℝ, 0 ≤ (f ⋆ k) x := by
    intro x
    rw [convolution_def]
    simp only [lsmul_apply, smul_eq_mul]
    exact integral_nonneg (fun u => mul_nonneg (hf0 u) (hk0 (x - u)))
  have hi := setIntegral_le_integral (s := Ioi (0 : ℝ)) hconv (Eventually.of_forall hconv0)
  have he : ∫ x : ℝ, (f ⋆ k) x = (∫ u : ℝ, f u) * h := by
    rw [integral_convolution (lsmul ℝ ℝ) hf hk]
    simp only [lsmul_apply, smul_eq_mul]
    rw [show (∫ t : ℝ, k t) = h from aux_backward_window_mass hh]
  calc (∫ x : ℝ in Ioi 0, ∫ u in x..(x + h), f u) =
        ∫ x : ℝ in Ioi 0, (f ⋆ k) x := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          exact (aux_window_eq_convolution f hh x).symm
    _ ≤ ∫ x : ℝ, (f ⋆ k) x := hi
    _ = h * ∫ u : ℝ, f u := by rw [he]; ring

/-- Sliding interval integrals of a positive half line function are integrable. -/
private theorem aux_positive_sliding_integrable {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (fun x : ℝ => ∫ u in x..(x + h), f u) (Ioi 0) := by
  classical
  let g : ℝ → ℝ := (Ioi 0).indicator f
  let k : ℝ → ℝ := (Ico (-h) 0).indicator (fun _ => (1 : ℝ))
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hk : Integrable k := by
    rw [show k = (Ico (-h) 0).indicator (fun _ => (1 : ℝ)) from rfl,
      integrable_indicator_iff measurableSet_Ico]
    exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hc : IntegrableOn (g ⋆ k) (Ioi 0) :=
    (hg.integrable_convolution (L := lsmul ℝ ℝ) hk).integrableOn
  apply hc.congr_fun _ measurableSet_Ioi
  intro x hx
  rw [show (g ⋆ k) x = ∫ u in x..(x + h), g u from aux_window_eq_convolution g hh x]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by linarith : x ≤ x + h)] at hu
  have hu0 : u ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi] at *; linarith [hu.1]
  exact indicator_of_mem hu0 f

/-- A single power has reciprocal ordinate decay on the dyadic enlargement `x..3x`. -/
private theorem aux_power_integral_bound (w : ℂ) (hw : w.re ≤ 2) (x : ℝ) (hx : 0 < x) :
    ‖∫ u in x..(3 * x), (u : ℂ) ^ w‖ ≤
      56 * x ^ (w.re + 1) / (1 + |w.im|) := by
  have hden : 0 < 1 + |w.im| := by positivity
  have hX : 0 < x ^ (w.re + 1) := Real.rpow_pos_of_pos hx _
  have hxp : x ^ w.re * x = x ^ (w.re + 1) := (Real.rpow_add_one hx.ne' _).symm
  have hpt (u : ℝ) (hu : u ∈ Set.uIoc x (3 * x)) :
      ‖(u : ℂ) ^ w‖ ≤ 9 * x ^ w.re := by
    rw [Set.uIoc_of_le (by linarith : x ≤ 3 * x)] at hu
    have hu0 : 0 < u := lt_trans hx hu.1
    have hratio1 : 1 ≤ u / x := (le_div_iff₀ hx).mpr (by linarith [hu.1])
    have hratio3 : u / x ≤ 3 := (div_le_iff₀ hx).mpr hu.2
    have hr := Real.rpow_le_rpow_of_exponent_le hratio1 hw
    have hsq : (u / x) ^ (2 : ℝ) ≤ 9 := by
      rw [Real.rpow_two]
      nlinarith
    rw [Real.div_rpow hu0.le hx.le] at hr
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hq : u ^ w.re / x ^ w.re ≤ 9 := hr.trans hsq
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hx _)).mp hq
  have hrough := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_pos (by linarith : 0 < 3 * x - x)] at hrough
  have hrough' : ‖∫ u in x..(3 * x), (u : ℂ) ^ w‖ ≤ 18 * x ^ (w.re + 1) := by
    calc _ ≤ 9 * x ^ w.re * (3 * x - x) := hrough
      _ = 18 * (x ^ w.re * x) := by ring
      _ = _ := by rw [hxp]
  by_cases him : |w.im| ≤ 1
  · apply hrough'.trans
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg hX.le (sub_nonneg.mpr him)]
  · have him1 : 1 < |w.im| := lt_of_not_ge him
    have him0 : 0 < |w.im| := by linarith
    have hne : w ≠ -1 := by
      intro he
      norm_num [he] at him1
    have hzero : (0 : ℝ) ∉ Set.uIcc x (3 * x) := by
      rw [Set.uIcc_of_le (by linarith : x ≤ 3 * x)]
      simp only [mem_Icc, not_and]
      intro h
      linarith
    rw [integral_cpow (Or.inr ⟨hne, hzero⟩), norm_div]
    have hscale : (3 * x) ^ (w.re + 1) ≤ 27 * x ^ (w.re + 1) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hx.le]
      have hb : (3 : ℝ) ^ (w.re + 1) ≤ 27 := by
        calc _ ≤ (3 : ℝ) ^ (3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 27 := by norm_num
      exact mul_le_mul_of_nonneg_right hb hX.le
    have hnum : ‖(↑(3 * x) : ℂ) ^ (w + 1) - (x : ℂ) ^ (w + 1)‖ ≤
        28 * x ^ (w.re + 1) := by
      have hn := norm_sub_le ((↑(3 * x) : ℂ) ^ (w + 1)) ((x : ℂ) ^ (w + 1))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re] at hn
      linarith
    have hnorm : |w.im| ≤ ‖w + 1‖ := by
      simpa only [Complex.add_im, Complex.one_im, add_zero] using Complex.abs_im_le_norm (w + 1)
    have hnpos : 0 < ‖w + 1‖ := lt_of_lt_of_le him0 hnorm
    calc _ ≤ (28 * x ^ (w.re + 1)) / ‖w + 1‖ :=
          div_le_div_of_nonneg_right hnum hnpos.le
      _ ≤ (28 * x ^ (w.re + 1)) / |w.im| :=
          div_le_div_of_nonneg_left (by positivity) him0 hnorm
      _ ≤ _ := by
        apply (div_le_div_iff₀ him0 hden).mpr
        nlinarith [mul_nonneg hX.le (sub_nonneg.mpr him1.le)]

/-- The integral of an unweighted power pair is bounded by the reciprocal separation. -/
private theorem aux_power_pair_integral (c d e f : ℂ) (he : e.re ≤ 1) (hf : f.re ≤ 1)
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
  have hb := aux_power_integral_bound (e + star f) (by
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
    linarith) x hx
  have hb' := mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg c) (norm_nonneg d))
  simp only [Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, ← sub_eq_add_neg] at hb'
  simp only [starRingEnd_apply] at hb'
  convert hb' using 1 <;> ring

/-- The finite weighted power square is bounded by its pair kernel sum. -/
private theorem aux_square_integral_le_pairs {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ i ∈ S, ContinuousOn (f i) (Set.Icc a b)) :
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

/-- Expansion of the finite power square into the reciprocal separation kernel. -/
private theorem aux_finite_power_energy {ι : Type*} (S : Finset ι) (c e : ι → ℂ)
    (he : ∀ i ∈ S, (e i).re ≤ 1) (x : ℝ) (hx : 0 < x) :
    (∫ u in x..(3 * x), ‖∑ i ∈ S, c i * (u : ℂ) ^ e i‖ ^ 2) ≤
      ∑ i ∈ S, ∑ j ∈ S,
        56 * ‖c i‖ * ‖c j‖ * x ^ ((e i).re + (e j).re + 1) /
          (1 + |(e i).im - (e j).im|) := by
  have hc (i : ι) : ContinuousOn (fun u : ℝ => c i * (u : ℂ) ^ e i) (Set.Icc x (3 * x)) := by
    intro u hu
    exact ((Complex.continuousAt_ofReal_cpow_const u (e i)
      (Or.inr (ne_of_gt (lt_of_lt_of_le hx hu.1)))).const_mul (c i)).continuousWithinAt
  refine (aux_square_integral_le_pairs S (fun i u => c i * (u : ℂ) ^ e i) x (3 * x)
    (by linarith) (fun i _ => hc i)).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact aux_power_pair_integral (c i) (c j) (e i) (e j) (he i hi) (he j hj) x hx

end

/-! ## Auxiliary lemmas on the low zero sum and on its derivative sum -/

/-- The low cutoff sums have finite support and retain the actual multiplicities. -/
private theorem aux_low_sum_finite (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
    ∃ S : Finset NontrivialZero,
      (∀ ρ : NontrivialZero, ρ ∈ S ↔ |ρ.1.im| ≤ x / h) ∧
      ∀ f : ℂ → ℂ,
        zeroSum (fun ρ => if |ρ.im| ≤ x / h then f ρ else 0) =
          ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * f ρ.1 := by
  classical
  have hf := PairKernel402.low_zeros_finite (x / h) (div_nonneg hx hh.le)
  refine ⟨hf.toFinset, fun ρ => hf.mem_toFinset, ?_⟩
  intro f
  unfold zeroSum
  rw [tsum_eq_sum (s := hf.toFinset)]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    have hp : |ρ.1.im| ≤ x / h := hf.mem_toFinset.mp hρ
    change (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      (if |ρ.1.im| ≤ x / h then f ρ.1 else 0) = _
    rw [if_pos hp]
  · intro ρ hρ
    have hp : ¬ (|ρ.1.im| ≤ x / h) := fun hc => hρ (hf.mem_toFinset.mpr hc)
    change (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      (if |ρ.1.im| ≤ x / h then f ρ.1 else 0) = 0
    rw [if_neg hp, mul_zero]

/-- The low zero derivative sum is continuous on positive arguments. -/
private theorem aux_derivative_continuousOn (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
    ContinuousOn (fun u : ℝ => zeroSum (fun ρ : ℂ =>
      if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0)) (Set.Ioi 0) := by
  obtain ⟨S, _, he⟩ := aux_low_sum_finite x h hx hh
  have heq : (fun u : ℝ => zeroSum (fun ρ : ℂ =>
        if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0)) =
      (fun u : ℝ => ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        ((u : ℂ) ^ (ρ.1 - 1))) := by
    funext u
    exact he (fun ρ => (u : ℂ) ^ (ρ - 1))
  rw [heq]
  apply continuousOn_finsetSum
  intro ρ hρ u hu
  exact ((Complex.continuousAt_ofReal_cpow_const u (ρ.1 - 1)
    (Or.inr (ne_of_gt hu))).const_mul _).continuousWithinAt

/-- Integrating the low zero derivative sum gives the low zero increment. -/
private theorem aux_zeros_eq_integral (x h t : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
    lowZeros x h t = ∫ u in t..(t + h), zeroSum (fun ρ : ℂ =>
      if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0) := by
  obtain ⟨S, _, he⟩ := aux_low_sum_finite x h hx hh
  have hD (u : ℝ) : zeroSum (fun ρ : ℂ => if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0) =
      ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * ((u : ℂ) ^ (ρ.1 - 1)) :=
    he (fun ρ => (u : ℂ) ^ (ρ - 1))
  unfold lowZeros
  rw [he]
  simp_rw [hD]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [intervalIntegral.integral_const_mul, integral_cpow
      (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith [ρ.2.2.1])),
      sub_add_cancel]
  · intro ρ hρ
    exact (intervalIntegral.intervalIntegrable_cpow'
      (by simp only [Complex.sub_re, Complex.one_re]; linarith [ρ.2.2.1])).const_mul _

/-- The finite low zero increment is a continuous function. -/
private theorem aux_lowZeros_continuous (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
    Continuous (fun t : ℝ => lowZeros x h t) := by
  obtain ⟨S, _, he⟩ := aux_low_sum_finite x h hx hh
  have heq : (fun t : ℝ => lowZeros x h t) =
      (fun t : ℝ => ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        (((t + h : ℝ) : ℂ) ^ ρ.1 - (t : ℂ) ^ ρ.1) / ρ.1) := by
    funext t
    simpa only [lowZeros, mul_div_assoc] using he (fun ρ =>
      (((t + h : ℝ) : ℂ) ^ ρ - (t : ℂ) ^ ρ) / ρ)
  rw [heq]
  apply continuous_finsetSum
  intro ρ hρ
  have hc := Complex.continuous_ofReal_cpow_const ρ.2.2.1
  exact (((hc.comp (continuous_id.add continuous_const)).sub hc).const_mul _).div_const _

/-- The Cauchy-Schwarz and sliding window steps: the increment average costs `h` squared. -/
private theorem aux_increment_average (x h : ℝ) (hx : 2 ≤ x) (hh : 2 ≤ h) (hhx : h ≤ x)
    (D : ℝ → ℂ) (hDcont : ContinuousOn D (Set.Ioi 0))
    (hDint : ∀ t : ℝ, lowZeros x h t = ∫ u in t..(t + h), D u) :
    IntervalIntegrable (fun t => ‖lowZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) ≤
        h ^ 2 * ∫ u in x..(3 * x), ‖D u‖ ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  have hcont := (aux_lowZeros_continuous x h hx0.le hh0).norm.pow 2
  have hDc : ContinuousOn D (Set.Icc x (3 * x)) :=
    hDcont.mono (fun u hu => lt_of_lt_of_le hx0 hu.1)
  let g : ℝ → ℝ := (Set.Icc x (3 * x)).indicator (fun u => ‖D u‖ ^ 2)
  have hg : Integrable g :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hDc.norm.pow 2).integrableOn_Icc
  have hg0 (u : ℝ) : 0 ≤ g u :=
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hgi : (∫ u : ℝ, g u) = ∫ u in x..(3 * x), ‖D u‖ ^ 2 := by
    rw [show g = (Set.Icc x (3 * x)).indicator (fun u => ‖D u‖ ^ 2) from rfl,
      integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : x ≤ 3 * x)]
  have hgshort (t : ℝ) (ht : t ∈ Set.Icc x (2 * x)) :
      (∫ u in t..(t + h), g u) = ∫ u in t..(t + h), ‖D u‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith : t ≤ t + h)] at hu
    exact Set.indicator_of_mem (show u ∈ Set.Icc x (3 * x) from
      ⟨by linarith [ht.1, hu.1], by linarith [ht.2, hu.2]⟩) _
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc x (2 * x)) :
      ‖lowZeros x h t‖ ^ 2 ≤ h * ∫ u in t..(t + h), g u := by
    have ht0 : 0 < t := lt_of_lt_of_le hx0 ht.1
    have hDt : ContinuousOn D (Set.Icc t (t + h)) :=
      hDcont.mono (fun u hu => lt_of_lt_of_le ht0 hu.1)
    have hDi : IntervalIntegrable D volume t (t + h) :=
      hDt.intervalIntegrable_of_Icc (by linarith)
    have hDsq : IntervalIntegrable (fun u : ℝ => ‖D u‖ ^ 2) volume t (t + h) :=
      (hDt.norm.pow 2).intervalIntegrable_of_Icc (by linarith)
    have hLp : MemLp D 2 (volume.restrict (Set.Ioc t (t + h))) :=
      (memLp_two_iff_integrable_sq_norm hDi.1.aestronglyMeasurable).mpr hDsq.1
    rw [hDint t, hgshort t ht]
    convert aux_norm_integral_square_le D t (t + h) (by linarith) hLp using 1 <;>
      congr 1 <;> ring
  have hsli := aux_positive_sliding_integrable hg.integrableOn hh0.le
  have hsmall : IntegrableOn (fun t : ℝ => ∫ u in t..(t + h), g u) (Set.Ioc x (2 * x)) :=
    hsli.mono_set (fun t ht => lt_of_lt_of_le hx0 ht.1.le)
  have hsquare := intervalIntegral.integral_mono_on (μ := volume)
    (by linarith : x ≤ 2 * x) (hcont.intervalIntegrable _ _)
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : x ≤ 2 * x) |>.mpr
      (hsmall.const_mul h)) hpoint
  rw [intervalIntegral.integral_const_mul] at hsquare
  have hsl0 (t : ℝ) : 0 ≤ ∫ u in t..(t + h), g u :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => hg0 u)
  have hsub : (Set.Ioc x (2 * x) : Set ℝ) ⊆ Set.Ioi 0 :=
    fun t ht => lt_of_lt_of_le hx0 ht.1.le
  have hdom := setIntegral_mono_set hsli (Filter.Eventually.of_forall hsl0) hsub.eventuallySubset
  have hsl := aux_sliding_integral_le hg hg0 hh0.le
  rw [hgi] at hsl
  have hdom' : (∫ t in x..(2 * x), ∫ u in t..(t + h), g u) ≤
      h * ∫ u in x..(3 * x), ‖D u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith : x ≤ 2 * x)]
    exact hdom.trans hsl
  refine ⟨hcont.intervalIntegrable _ _, ?_⟩
  have hlast := mul_le_mul_of_nonneg_left hdom' hh0.le
  calc _ ≤ h * ∫ t in x..(2 * x), ∫ u in t..(t + h), g u := hsquare
    _ ≤ h * (h * ∫ u in x..(3 * x), ‖D u‖ ^ 2) := hlast
    _ = _ := by ring

/-- Expansion and integration of the derivative square, with the reciprocal kernel retained. -/
private theorem aux_derivative_pair_energy : 1 / 2 < Theta → Theta < 1 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      (∫ u in x..(3 * x), ‖zeroSum (fun ρ : ℂ =>
        if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0)‖ ^ 2) ≤
        K * x ^ (2 * Theta - 1) * lowPairWeight x h := by
  intro hlo hhi
  refine ⟨56, by norm_num, ?_⟩
  intro x h hx hh hhx
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  obtain ⟨S, hS, he⟩ := aux_low_sum_finite x h hx0.le hh0
  have hD (u : ℝ) : zeroSum (fun ρ : ℂ => if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0) =
      ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (u : ℂ) ^ (ρ.1 - 1) :=
    he (fun ρ => (u : ℂ) ^ (ρ - 1))
  have hb := aux_finite_power_energy S
    (fun ρ => (analyticOrderNatAt riemannZeta ρ.1 : ℂ)) (fun ρ => ρ.1 - 1)
    (fun ρ _ => by simp only [Complex.sub_re, Complex.one_re]; linarith [ρ.2.2.2]) x hx0
  simp only [Complex.norm_natCast, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, sub_zero] at hb
  have hweight : lowPairWeight x h = ∑ ρ ∈ S, ∑ σ ∈ S,
      (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (analyticOrderNatAt riemannZeta σ.1 : ℝ) /
        (1 + |ρ.1.im - σ.1.im|) := by
    simpa only [lowPairWeight, LeanLab.PNTPort.Selberg.mz] using
      PairKernel402.low_pair_sum_eq_finite (x / h) S hS
  calc (∫ u in x..(3 * x), ‖zeroSum (fun ρ : ℂ =>
        if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0)‖ ^ 2)
      = ∫ u in x..(3 * x), ‖∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
          (u : ℂ) ^ (ρ.1 - 1)‖ ^ 2 := by simp_rw [hD]
    _ ≤ _ := hb
    _ ≤ ∑ ρ ∈ S, ∑ σ ∈ S, (56 * x ^ (2 * Theta - 1)) *
        ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
          (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|)) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      apply Finset.sum_le_sum
      intro σ hσ
      have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
        (show ρ.1.re - 1 + (σ.1.re - 1) + 1 ≤ 2 * Theta - 1 from by
          linarith [GSCor2.re_le_Theta ρ, GSCor2.re_le_Theta σ])
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤
        56 * (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
          (analyticOrderNatAt riemannZeta σ.1 : ℝ) by positivity)
      have hd := div_le_div_of_nonneg_right hm (show 0 ≤ 1 + |ρ.1.im - σ.1.im| by positivity)
      convert hd using 1 <;> ring
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [← hweight]

/-- LEAF. BHMS page 18, the Cauchy Schwarz step, change of order, and pair integral display.
The zero sum square is interval integrable. Oscillatory power integration gives the pair kernel.
This leaf contains no ordinate count estimate. -/
theorem low_pair_integral : 1 / 2 < Theta → Theta < 1 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖lowZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) ≤
        K * h ^ 2 * x ^ (2 * Theta - 1) * lowPairWeight x h := by
  intro hlo hhi
  obtain ⟨K, hK, hE⟩ := aux_derivative_pair_energy hlo hhi
  refine ⟨K, hK, ?_⟩
  intro x h hx hh hhx
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  obtain ⟨hi, hb⟩ := aux_increment_average x h hx hh hhx
    (fun u : ℝ => zeroSum (fun ρ : ℂ => if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0))
    (aux_derivative_continuousOn x h hx0.le hh0)
    (fun t => aux_zeros_eq_integral x h t hx0.le hh0)
  refine ⟨hi, hb.trans ?_⟩
  calc h ^ 2 * (∫ u in x..(3 * x), ‖zeroSum (fun ρ : ℂ =>
        if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0)‖ ^ 2)
      ≤ h ^ 2 * (K * x ^ (2 * Theta - 1) * lowPairWeight x h) :=
        mul_le_mul_of_nonneg_left (hE x h hx hh hhx) (sq_nonneg h)
    _ = _ := by ring

/-- LEAF. BHMS page 18, the two final low zero displays using Lemma 6.
Local zero counting bounds the reciprocal separation sum and the number of low ordinates.
The source log cubed bound is weakened to log to the fourth on x at least two. -/
theorem low_pair_count : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      lowPairWeight x h ≤ C * (x / h) * Real.log x ^ 4 := by
  simpa only [lowPairWeight] using PairKernel402.low_pair_count_ts

/-- The exact low_zero_variance target follows from the pair integral and pair count leaves.
CONDITIONAL ON low_pair_integral. -/
theorem low_zero_variance_assembled : 1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖lowZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) ≤
        C * h * x ^ (2 * Theta) * Real.log x ^ 4 := by
  intro hlo hhi
  obtain ⟨K, hK, hk⟩ := low_pair_integral hlo hhi
  obtain ⟨C, hC, hc⟩ := low_pair_count
  refine ⟨K * C, by positivity, ?_⟩
  intro x h hx hh hhx
  obtain ⟨hi, hb⟩ := hk x h hx hh hhx
  refine ⟨hi, hb.trans ?_⟩
  have hmul := mul_le_mul_of_nonneg_left (hc x h hx hh hhx)
    (show 0 ≤ K * h ^ 2 * x ^ (2 * Theta - 1) by positivity)
  have hx0 : 0 < x := by linarith
  have hh0 : h ≠ 0 := by linarith
  have hp : x ^ (2 * Theta - 1) * x = x ^ (2 * Theta) := by
    have he := Real.rpow_add hx0 (2 * Theta - 1) 1
    have hexp : 2 * Theta - 1 + 1 = 2 * Theta := by ring
    rw [hexp, Real.rpow_one] at he
    exact he.symm
  calc K * h ^ 2 * x ^ (2 * Theta - 1) * lowPairWeight x h
      ≤ (K * h ^ 2 * x ^ (2 * Theta - 1)) * (C * (x / h) * Real.log x ^ 4) := hmul
    _ = (K * C) * h * (x ^ (2 * Theta - 1) * x) * Real.log x ^ 4 := by
      field_simp [hh0]
      <;> ring
    _ = _ := by rw [hp]

example : type_of% low_zero_variance = type_of% low_zero_variance_assembled := rfl

end LeanLab.GoldbachAverage.Decomp402c
