import LeanLab.GoldbachAverage.Decomp402c
import LeanLab.GoldbachAverage.Sliding124
import LeanLab.GoldbachAverage.WindowCauchy444
import LeanLab.GoldbachAverage.FinitePower444

/-!
BHMS, https://arxiv.org/abs/1704.06103v2 page 18, first four low zero displays.
The derivative averaging step and the oscillatory power integral are separate tasks.
The reciprocal zero count is already proved and is not cut again.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp444b
open MeasureTheory
open Decomp287d Decomp402c

/-- The finite low zero derivative sum in the first display on BHMS page 18.
Multiplicities agree with the lowZeros definition. -/
def lowDerivative (x h u : ℝ) : ℂ :=
  zeroSum (fun ρ => if |ρ.im| ≤ x / h then (u : ℂ) ^ (ρ - 1) else 0)

/-- BHMS page 18 low cutoff sums have finite support and retain their multiplicities. -/
theorem low_sum_finite (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
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
    change (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (if |ρ.1.im| ≤ x / h then f ρ.1 else 0) = _
    rw [if_pos hp]
  · intro ρ hρ
    have hp : ¬ (|ρ.1.im| ≤ x / h) := fun hc => hρ (hf.mem_toFinset.mpr hc)
    change (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (if |ρ.1.im| ≤ x / h then f ρ.1 else 0) = 0
    rw [if_neg hp, mul_zero]

/-- BHMS page 18 first display, the low derivative sum is continuous on positive arguments. -/
theorem lowDerivative_continuousOn (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
    ContinuousOn (fun u : ℝ => lowDerivative x h u) (Set.Ioi 0) := by
  obtain ⟨S, _, he⟩ := low_sum_finite x h hx hh
  have heq : (fun u : ℝ => lowDerivative x h u) =
      (fun u : ℝ => ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
        ((u : ℂ) ^ (ρ.1 - 1))) := by
    funext u
    exact he (fun ρ => (u : ℂ) ^ (ρ - 1))
  rw [heq]
  apply continuousOn_finsetSum
  intro ρ hρ u hu
  exact ((Complex.continuousAt_ofReal_cpow_const u (ρ.1 - 1)
    (Or.inr (ne_of_gt hu))).const_mul _).continuousWithinAt

/-- BHMS page 18 first display, integrating the low derivative gives the low zero increment. -/
theorem lowZeros_eq_integral (x h t : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
    lowZeros x h t = ∫ u in t..(t + h), lowDerivative x h u := by
  obtain ⟨S, _, he⟩ := low_sum_finite x h hx hh
  have hD (u : ℝ) : lowDerivative x h u =
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

/-- BHMS page 18, the finite low zero increment is a continuous function. -/
theorem lowZeros_continuous (x h : ℝ) (hx : 0 ≤ x) (hh : 0 < h) :
    Continuous (fun t : ℝ => lowZeros x h t) := by
  obtain ⟨S, _, he⟩ := low_sum_finite x h hx hh
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

/-- LEAF. BHMS page 18 first three displays, before expanding the square.
Cauchy Schwarz and the sliding interval multiplicity bound give h squared.
This assertion contains no oscillatory pair estimate or zero count. -/
theorem low_increment_average (x h : ℝ) (hx : 2 ≤ x) (hh : 2 ≤ h) (hhx : h ≤ x) :
    IntervalIntegrable (fun t => ‖lowZeros x h t‖ ^ 2) volume x (2 * x) ∧
    (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) ≤
      h ^ 2 * ∫ u in x..(3 * x), ‖lowDerivative x h u‖ ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  have hcont := (lowZeros_continuous x h hx0.le hh0).norm.pow 2
  have hD := lowDerivative_continuousOn x h hx0.le hh0
  have hDc : ContinuousOn (fun u : ℝ => lowDerivative x h u) (Set.Icc x (3 * x)) :=
    hD.mono (fun u hu => lt_of_lt_of_le hx0 hu.1)
  let g : ℝ → ℝ := (Set.Icc x (3 * x)).indicator (fun u => ‖lowDerivative x h u‖ ^ 2)
  have hg : Integrable g :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hDc.norm.pow 2).integrableOn_Icc
  have hg0 (u : ℝ) : 0 ≤ g u := by
    exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hgi : (∫ u : ℝ, g u) = ∫ u in x..(3 * x), ‖lowDerivative x h u‖ ^ 2 := by
    rw [show g = (Set.Icc x (3 * x)).indicator (fun u => ‖lowDerivative x h u‖ ^ 2) from rfl,
      integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : x ≤ 3 * x)]
  have hgshort (t : ℝ) (ht : t ∈ Set.Icc x (2 * x)) :
      (∫ u in t..(t + h), g u) = ∫ u in t..(t + h), ‖lowDerivative x h u‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith : t ≤ t + h)] at hu
    exact Set.indicator_of_mem (show u ∈ Set.Icc x (3 * x) from
      ⟨by linarith [ht.1, hu.1], by linarith [ht.2, hu.2]⟩) _
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc x (2 * x)) :
      ‖lowZeros x h t‖ ^ 2 ≤ h * ∫ u in t..(t + h), g u := by
    have ht0 : 0 < t := lt_of_lt_of_le hx0 ht.1
    have hDt : ContinuousOn (fun u : ℝ => lowDerivative x h u) (Set.Icc t (t + h)) :=
      hD.mono (fun u hu => lt_of_lt_of_le ht0 hu.1)
    have hDi : IntervalIntegrable (fun u : ℝ => lowDerivative x h u) volume t (t + h) :=
      hDt.intervalIntegrable_of_Icc (by linarith)
    have hDsq : IntervalIntegrable (fun u : ℝ => ‖lowDerivative x h u‖ ^ 2) volume t (t + h) :=
      (hDt.norm.pow 2).intervalIntegrable_of_Icc (by linarith)
    have hLp : MemLp (fun u : ℝ => lowDerivative x h u) 2
        (volume.restrict (Set.Ioc t (t + h))) :=
      (memLp_two_iff_integrable_sq_norm hDi.1.aestronglyMeasurable).mpr hDsq.1
    rw [lowZeros_eq_integral x h t hx0.le hh0, hgshort t ht]
    convert WindowCauchy444.norm_integral_square_le (fun u => lowDerivative x h u)
      t (t + h) (by linarith) hLp using 1 <;> congr 1 <;> ring
  have hsli := Sliding124.positive_sliding_integrable hg.integrableOn hh0.le
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
  have hsl := Sliding124.sliding_integral_le hg hg0 hh0.le
  rw [hgi] at hsl
  have hdom' : (∫ t in x..(2 * x), ∫ u in t..(t + h), g u) ≤
      h * ∫ u in x..(3 * x), ‖lowDerivative x h u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith : x ≤ 2 * x)]
    exact hdom.trans hsl
  refine ⟨hcont.intervalIntegrable _ _, ?_⟩
  have hlast := mul_le_mul_of_nonneg_left hdom' hh0.le
  calc _ ≤ h * ∫ t in x..(2 * x), ∫ u in t..(t + h), g u := hsquare
    _ ≤ h * (h * ∫ u in x..(3 * x), ‖lowDerivative x h u‖ ^ 2) := hlast
    _ = _ := by ring

/-- LEAF. BHMS page 18, expansion and integration of the derivative square.
Integrate each complex power pair over x to three x and use beta at most Theta.
The reciprocal separation kernel is retained without estimating its zero count. -/
theorem low_derivative_pair_energy : 1 / 2 < Theta → Theta < 1 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      (∫ u in x..(3 * x), ‖lowDerivative x h u‖ ^ 2) ≤
        K * x ^ (2 * Theta - 1) * lowPairWeight x h := by
  intro hlo hhi
  refine ⟨56, by norm_num, ?_⟩
  intro x h hx hh hhx
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  obtain ⟨S, hS, he⟩ := low_sum_finite x h hx0.le hh0
  have hD (u : ℝ) : lowDerivative x h u =
      ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (u : ℂ) ^ (ρ.1 - 1) :=
    he (fun ρ => (u : ℂ) ^ (ρ - 1))
  have hb := FinitePower444.finite_power_energy S
    (fun ρ => (analyticOrderNatAt riemannZeta ρ.1 : ℂ)) (fun ρ => ρ.1 - 1)
    (fun ρ _ => by simp only [Complex.sub_re, Complex.one_re]; linarith [ρ.2.2.2]) x hx0
  simp only [Complex.norm_natCast, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, sub_zero] at hb
  have hweight : lowPairWeight x h = ∑ ρ ∈ S, ∑ σ ∈ S,
      (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (analyticOrderNatAt riemannZeta σ.1 : ℝ) /
        (1 + |ρ.1.im - σ.1.im|) := by
    simpa only [lowPairWeight, LeanLab.PNTPort.Selberg.mz] using
      PairKernel402.low_pair_sum_eq_finite (x / h) S hS
  calc (∫ u in x..(3 * x), ‖lowDerivative x h u‖ ^ 2)
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

/-- The exact low_pair_integral target follows from the two smaller page 18 steps.
The averaging and pair integration components are both proved. -/
theorem low_pair_integral_assembled : 1 / 2 < Theta → Theta < 1 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      IntervalIntegrable (fun t => ‖lowZeros x h t‖ ^ 2) volume x (2 * x) ∧
      (∫ t in x..(2 * x), ‖lowZeros x h t‖ ^ 2) ≤
        K * h ^ 2 * x ^ (2 * Theta - 1) * lowPairWeight x h := by
  intro hlo hhi
  obtain ⟨K, hK, hE⟩ := low_derivative_pair_energy hlo hhi
  refine ⟨K, hK, ?_⟩
  intro x h hx hh hhx
  obtain ⟨hi, hb⟩ := low_increment_average x h hx hh hhx
  refine ⟨hi, hb.trans ?_⟩
  calc h ^ 2 * (∫ u in x..(3 * x), ‖lowDerivative x h u‖ ^ 2)
      ≤ h ^ 2 * (K * x ^ (2 * Theta - 1) * lowPairWeight x h) :=
        mul_le_mul_of_nonneg_left (hE x h hx hh hhx) (sq_nonneg h)
    _ = _ := by ring

example : type_of% Decomp402c.low_pair_integral = type_of% low_pair_integral_assembled := rfl

end LeanLab.GoldbachAverage.Decomp444b
