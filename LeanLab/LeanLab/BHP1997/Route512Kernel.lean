import Mathlib

/-
P0069, Baker, Harman and Pintz 1997, the exceptional set for Goldbach's problem in
short intervals. This file serves pages 8 and 9, display 2.10 and the reduction to
display 2.11: the Gallagher type window inequality. Parseval or Bessel on a full period,
Cauchy Schwarz and a 1-periodic kernel turn a uniform local energy bound for S2 on
windows of radius 1/H into the mean square bound for the Fourier coefficients of S1 S2
on the minor arc set over an interval of H frequencies.

The proof here uses the kernel form of the argument. With h = 1/(8H) and N1 the middle
frequency, the kernel is e(N1 u) cut off to the points u within h of an integer, and
G(α) is the integral over m of S1(t) S2(t) times the kernel at α - t. The Fourier
coefficient of G at N is the coefficient of S1 S2 on m times the coefficient of the
kernel, which is bounded below for the H frequencies in range. Bessel bounds the
coefficients of G by its mean square, and pointwise Cauchy Schwarz bounds G by the
windowed energy of S1 times three local energies of S2.

All statements are generic in the measurable set m inside one period and in the two
coefficient sequences. The file imports Mathlib only.

AI wrote the Lean code. Goldbach is open.
-/

open MeasureTheory Set
open scoped ComplexConjugate

namespace LeanLab.BHP1997.Route512

/-- P0069 page 9, before 2.11: a bounded measurable function is integrable for a finite
measure. Bookkeeping for every integral in the Gallagher step. -/
private theorem integrable_of_bound512 {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound hf C (Filter.Eventually.of_forall hb)

/-- P0069 page 5: the integer exponential e(n t) is continuous in the real variable. -/
private theorem continuous_fourier512 (n : ℤ) :
    Continuous (fun t : ℝ => @fourier 1 n (t : AddCircle (1 : ℝ))) :=
  (map_continuous (fourier n)).comp (AddCircle.continuous_mk' 1)

/-- P0069 page 5: the integer exponential e(n t) has modulus one. -/
private theorem norm_fourier512 (n : ℤ) (t : ℝ) :
    ‖@fourier 1 n (t : AddCircle (1 : ℝ))‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- P0069 page 9, display 2.10: e(n α) = e(n t) e(n (α - t)), the shift used to compute
the Fourier coefficients of the windowed convolution. -/
private theorem fourier_shift512 (n : ℤ) (α t : ℝ) :
    @fourier 1 n (α : AddCircle (1 : ℝ)) =
      @fourier 1 n (t : AddCircle (1 : ℝ)) *
        @fourier 1 n ((α - t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0069 page 5: the integer exponential e(n t) has period one. -/
private theorem fourier_periodic512 (n : ℤ) :
    Function.Periodic (fun t : ℝ => @fourier 1 n (t : AddCircle (1 : ℝ))) 1 := by
  intro t
  simp only
  rw [AddCircle.coe_add_period]

/-- P0069 page 5: integer exponentials are orthogonal on any complete period. -/
private theorem integral_fourier512 (n : ℤ) (c : ℝ) :
    (∫ t in c..c + 1, @fourier 1 n (t : AddCircle (1 : ℝ))) = if n = 0 then 1 else 0 := by
  have h := fourierCoeff_eq_intervalIntegral (T := (1 : ℝ)) (@fourier 1 n) 0 c
  simp only [one_div_one, one_smul] at h
  rw [fourierCoeff_fourier] at h
  simpa [Pi.single_apply, eq_comm] using h.symm

/-- P0069 page 9, Parseval before 2.11: expand the squared modulus of a trigonometric
polynomial. -/
private theorem poly_norm_sq512 (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (‖∑ k ∈ S, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ ^ 2 : ℂ) =
      ∑ k ∈ S, ∑ m ∈ S, (conj (a k) * a m) *
        @fourier 1 (-(k : ℤ) + (m : ℤ)) (t : AddCircle (1 : ℝ)) := by
  rw [← Complex.conj_mul']
  simp only [map_sum, map_mul, ← fourier_neg, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro m hm
  rw [fourier_add]
  ring

/-- P0069 page 9, Parseval before 2.11: the exact energy identity for a trigonometric
polynomial on a complete period. -/
private theorem parseval512 (S : Finset ℕ) (a : ℕ → ℂ) (c : ℝ) :
    (∫ t in Ioc c (c + 1),
        ‖∑ k ∈ S, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ ^ 2) =
      ∑ k ∈ S, ‖a k‖ ^ 2 := by
  rw [← intervalIntegral.integral_of_le (by linarith)]
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [Complex.ofReal_pow, poly_norm_sq512]
  have hc (k m : ℕ) : Continuous (fun t : ℝ => (conj (a k) * a m) *
      @fourier 1 (-(k : ℤ) + (m : ℤ)) (t : AddCircle (1 : ℝ))) :=
    continuous_const.mul (continuous_fourier512 _)
  rw [intervalIntegral.integral_finsetSum (fun k hk =>
    (continuous_finsetSum S fun m hm => hc k m).intervalIntegrable _ _)]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_finsetSum (fun m hm => (hc k m).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_fourier512]
  have he (m : ℕ) : -(k : ℤ) + (m : ℤ) = 0 ↔ m = k := by omega
  simp [he, hk, Complex.conj_mul']

/-- P0069 page 9, display 2.10: the Cauchy Schwarz inequality for bounded real functions
on a finite measure space, proved by the discriminant of a nonnegative quadratic. -/
private theorem cauchy_schwarz512 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (f g : X → ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (Cf Cg : ℝ) (hfb : ∀ x, |f x| ≤ Cf)
    (hgb : ∀ x, |g x| ≤ Cg) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have hf2 : Integrable (fun x => f x ^ 2) μ :=
    integrable_of_bound512 (hf.pow 2) (Cf ^ 2) fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hfb x) 2
  have hg2 : Integrable (fun x => g x ^ 2) μ :=
    integrable_of_bound512 (hg.pow 2) (Cg ^ 2) fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hgb x) 2
  have hfg : Integrable (fun x => f x * g x) μ :=
    integrable_of_bound512 (hf.mul hg) (Cf * Cg) fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hfb x) (hgb x) (abs_nonneg _) ((abs_nonneg _).trans (hfb x))
  have key : ∀ x : ℝ, 0 ≤ (∫ a, g a ^ 2 ∂μ) * (x * x) + (-2 * ∫ a, f a * g a ∂μ) * x
      + ∫ a, f a ^ 2 ∂μ := by
    intro x
    have h0 : 0 ≤ ∫ a, (f a - x * g a) ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
    have h1 : (∫ a, (f a - x * g a) ^ 2 ∂μ) =
        (∫ a, f a ^ 2 ∂μ) - 2 * x * (∫ a, f a * g a ∂μ) + x ^ 2 * ∫ a, g a ^ 2 ∂μ := by
      have e : (fun a => (f a - x * g a) ^ 2) =
          fun a => (f a ^ 2 - 2 * x * (f a * g a)) + x ^ 2 * g a ^ 2 := by
        ext a
        ring
      have i1 : Integrable (fun a => 2 * x * (f a * g a)) μ := hfg.const_mul _
      have i2 : Integrable (fun a => f a ^ 2 - 2 * x * (f a * g a)) μ := hf2.sub i1
      have i3 : Integrable (fun a => x ^ 2 * g a ^ 2) μ := hg2.const_mul _
      rw [e, integral_add i2 i3, integral_sub hf2 i1, integral_const_mul, integral_const_mul]
    rw [h1] at h0
    nlinarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

/-- P0069 page 9, display 2.10: the integral of a shifted 1-periodic function over one
period does not depend on the shift. -/
private theorem periodic_shift512 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hper : Function.Periodic g 1) (c t : ℝ) :
    (∫ α in Ioc c (c + 1), g (α - t)) = ∫ u in Ioc (-1 / 2 : ℝ) (1 / 2), g u := by
  rw [← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_comp_sub_right (fun u => g u) t,
    show c + 1 - t = (c - t) + 1 by ring, hper.intervalIntegral_add_eq (c - t) (-1 / 2)]
  norm_num

/-- P0069 page 9, display 2.10: Fubini for a bounded function against a bounded 1-periodic
kernel. The convolution over one period factors as the integral of the function times
the integral of the kernel over one period. -/
private theorem fubini_kernel512 {𝕜 : Type*} [RCLike 𝕜] (c : ℝ) (s : Set ℝ)
    (hsc : s ⊆ Ioc c (c + 1)) (f g : ℝ → 𝕜) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) (Cf Cg : ℝ) (hfb : ∀ t, ‖f t‖ ≤ Cf) (hgb : ∀ u, ‖g u‖ ≤ Cg)
    (hper : Function.Periodic g 1) :
    Integrable (fun α => ∫ t in s, f t * g (α - t)) (volume.restrict (Ioc c (c + 1))) ∧
    (∫ α in Ioc c (c + 1), ∫ t in s, f t * g (α - t)) =
      (∫ t in s, f t) * ∫ u in Ioc (-1 / 2 : ℝ) (1 / 2), g u := by
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono hsc) measure_Ioc_lt_top⟩
  have hmeas : StronglyMeasurable (Function.uncurry fun (α t : ℝ) => f t * g (α - t)) :=
    (hf.comp_measurable measurable_snd).mul
      (hg.comp_measurable (measurable_fst.sub measurable_snd))
  have hint : Integrable (Function.uncurry fun (α t : ℝ) => f t * g (α - t))
      ((volume.restrict (Ioc c (c + 1))).prod (volume.restrict s)) :=
    integrable_of_bound512 hmeas.aestronglyMeasurable (Cf * Cg) fun p => by
      obtain ⟨α, t⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [norm_mul]
      exact mul_le_mul (hfb t) (hgb _) (norm_nonneg _) ((norm_nonneg _).trans (hfb t))
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [integral_integral_swap hint]
  have hin : ∀ t, (∫ α in Ioc c (c + 1), f t * g (α - t)) =
      f t * ∫ u in Ioc (-1 / 2 : ℝ) (1 / 2), g u := by
    intro t
    rw [integral_const_mul, periodic_shift512 g hper c t]
  simp_rw [hin]
  rw [integral_mul_const]

/-- P0069 page 9, the Parseval or Bessel step before 2.11: for a bounded measurable
function on one period, the squared Fourier coefficients at distinct integer frequencies
sum to at most the mean square. Proved by duality from Cauchy Schwarz and Parseval. -/
private theorem bessel512 (c : ℝ) (G : ℝ → ℂ)
    (hGm : AEStronglyMeasurable G (volume.restrict (Ioc c (c + 1)))) (C : ℝ)
    (hGb : ∀ α, ‖G α‖ ≤ C) (K : Finset ℕ) :
    ∑ N ∈ K, ‖∫ α in Ioc c (c + 1),
        G α * @fourier 1 (-(N : ℤ)) (α : AddCircle (1 : ℝ))‖ ^ 2 ≤
      ∫ α in Ioc c (c + 1), ‖G α‖ ^ 2 := by
  set μ := volume.restrict (Ioc c (c + 1)) with hμ
  set cN : ℕ → ℂ := fun N =>
    ∫ α, G α * @fourier 1 (-(N : ℤ)) (α : AddCircle (1 : ℝ)) ∂μ with hcN
  set X : ℝ := ∑ N ∈ K, ‖cN N‖ ^ 2 with hX
  set Q : ℝ → ℂ := fun α => ∑ N ∈ K, cN N * @fourier 1 (N : ℤ) (α : AddCircle (1 : ℝ))
    with hQ
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun N _ => sq_nonneg _
  have hQc : Continuous Q :=
    continuous_finsetSum _ fun N _ => continuous_const.mul (continuous_fourier512 _)
  have hQb : ∀ α, ‖Q α‖ ≤ ∑ N ∈ K, ‖cN N‖ := fun α => by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun N _ => ?_)
    rw [norm_mul, norm_fourier512, mul_one]
  have hterm : ∀ N : ℕ, Integrable
      (fun α => G α * @fourier 1 (-(N : ℤ)) (α : AddCircle (1 : ℝ))) μ := fun N =>
    integrable_of_bound512 (hGm.mul (continuous_fourier512 _).aestronglyMeasurable) C
      fun α => by
        rw [norm_mul, norm_fourier512, mul_one]
        exact hGb α
  have h1 : (X : ℂ) = ∫ α, G α * conj (Q α) ∂μ := by
    have e : ∀ α, G α * conj (Q α) = ∑ N ∈ K, conj (cN N) *
        (G α * @fourier 1 (-(N : ℤ)) (α : AddCircle (1 : ℝ))) := by
      intro α
      simp only [hQ, map_sum, map_mul, ← fourier_neg, Finset.mul_sum]
      exact Finset.sum_congr rfl fun N _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun N _ => (hterm N).const_mul _]
    simp_rw [integral_const_mul]
    rw [hX]
    push_cast
    exact Finset.sum_congr rfl fun N _ => (Complex.conj_mul' (cN N)).symm
  have h2 : X ≤ ∫ α, ‖G α‖ * ‖Q α‖ ∂μ := by
    have hXn : X = ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hX0]
    rw [hXn, h1]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    ext α
    rw [norm_mul, RCLike.norm_conj]
  have h3 := cauchy_schwarz512 μ (fun α => ‖G α‖) (fun α => ‖Q α‖) hGm.norm
    hQc.norm.aestronglyMeasurable C (∑ N ∈ K, ‖cN N‖)
    (fun α => by rw [abs_norm]; exact hGb α) (fun α => by rw [abs_norm]; exact hQb α)
  have h4 : (∫ α, ‖Q α‖ ^ 2 ∂μ) = X := parseval512 K cN c
  have hG0 : 0 ≤ ∫ α, ‖G α‖ ^ 2 ∂μ := integral_nonneg fun α => sq_nonneg _
  rw [h4] at h3
  by_contra hcon
  push Not at hcon
  have ha : X * X ≤ (∫ α, ‖G α‖ * ‖Q α‖ ∂μ) * ∫ α, ‖G α‖ * ‖Q α‖ ∂μ :=
    mul_self_le_mul_self hX0 h2
  have hb : (∫ α, ‖G α‖ ^ 2 ∂μ) * X < X * X :=
    mul_lt_mul_of_pos_right hcon (lt_of_le_of_lt hG0 hcon)
  nlinarith

/-- P0069 page 9, display 2.10: a window indicator is nonnegative. -/
private theorem ind_nonneg512 (s : Set ℝ) (u : ℝ) : 0 ≤ s.indicator (fun _ => (1 : ℝ)) u := by
  by_cases hu : u ∈ s <;> simp [hu]

/-- P0069 page 9, display 2.10: a window indicator is at most one. -/
private theorem ind_le_one512 (s : Set ℝ) (u : ℝ) : s.indicator (fun _ => (1 : ℝ)) u ≤ 1 := by
  by_cases hu : u ∈ s <;> simp [hu]

/-- P0069 page 9, display 2.10: a window indicator equals its square. -/
private theorem ind_sq512 (s : Set ℝ) (u : ℝ) :
    s.indicator (fun _ => (1 : ℝ)) u ^ 2 = s.indicator (fun _ => (1 : ℝ)) u := by
  by_cases hu : u ∈ s <;> simp [hu]

/-- P0069 page 9, display 2.10: the 1-periodic window, the points within h of an
integer, is measurable. -/
private theorem measurableSet_window512 (h : ℝ) :
    MeasurableSet {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h} := by
  have e : {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h} = ⋃ j : ℤ, {u : ℝ | |u - (j : ℝ)| < h} := by
    ext u
    simp
  rw [e]
  exact MeasurableSet.iUnion fun j =>
    measurableSet_lt (continuous_id.sub continuous_const).abs.measurable measurable_const

/-- P0069 page 9, display 2.10: the periodic window is invariant under the shift by one. -/
private theorem window_add_one512 (h u : ℝ) :
    (u + 1) ∈ {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h} ↔
      u ∈ {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h} := by
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j - 1, ?_⟩
    rw [Int.cast_sub, Int.cast_one, show u - ((j : ℝ) - 1) = u + 1 - j by ring]
    exact hj
  · rintro ⟨j, hj⟩
    refine ⟨j + 1, ?_⟩
    rw [Int.cast_add, Int.cast_one, show u + 1 - ((j : ℝ) + 1) = u - j by ring]
    exact hj

/-- P0069 page 9, display 2.10: on the centred period the periodic window is the
interval of radius h around zero, for h at most one quarter. -/
private theorem window_center512 (h : ℝ) (hh : h ≤ 1 / 4) (u : ℝ)
    (hu : u ∈ Ioc (-1 / 2 : ℝ) (1 / 2)) :
    u ∈ {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h} ↔ u ∈ Ioo (-h) h := by
  simp only [mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨j, hj⟩
    rw [abs_lt] at hj
    have h1 : j < 1 := by
      exact_mod_cast (by linarith [hu.2] : (j : ℝ) < 1)
    have h2 : -1 < j := by
      exact_mod_cast (by linarith [hu.1] : (-1 : ℝ) < j)
    have hj0 : j = 0 := by omega
    subst hj0
    rw [Int.cast_zero, sub_zero] at hj
    exact hj
  · intro hu'
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, sub_zero, abs_lt]
    exact hu'

/-- P0069 page 9, display 2.10: a 1-periodic function cut off by the periodic window is
1-periodic. -/
private theorem window_indicator_periodic512 {E : Type*} [Zero E] (h : ℝ) (φ : ℝ → E)
    (hφ : Function.Periodic φ 1) :
    Function.Periodic ({u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator φ) 1 := by
  intro u
  by_cases hu : u ∈ {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}
  · rw [indicator_of_mem hu, indicator_of_mem ((window_add_one512 h u).mpr hu), hφ u]
  · rw [indicator_of_notMem hu,
      indicator_of_notMem fun hc => hu ((window_add_one512 h u).mp hc)]

/-- P0069 page 9, display 2.10: the integral over the centred period of a function cut
off by the periodic window is its integral over the interval of radius h. -/
private theorem window_integral512 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 4) (φ : ℝ → E) :
    (∫ u in Ioc (-1 / 2 : ℝ) (1 / 2),
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator φ u) =
      ∫ u in Ioo (-h) h, φ u := by
  have e : EqOn ({u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator φ)
      ((Ioo (-h) h).indicator φ) (Ioc (-1 / 2 : ℝ) (1 / 2)) := by
    intro u hu
    by_cases hw : u ∈ Ioo (-h) h
    · rw [indicator_of_mem hw, indicator_of_mem ((window_center512 h hh u hu).mpr hw)]
    · rw [indicator_of_notMem hw,
        indicator_of_notMem fun hc => hw ((window_center512 h hh u hu).mp hc)]
  have hsub : Ioo (-h) h ⊆ Ioc (-1 / 2 : ℝ) (1 / 2) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  rw [setIntegral_congr_fun measurableSet_Ioc e, setIntegral_indicator measurableSet_Ioo,
    inter_eq_self_of_subset_right hsub]

/-- P0069 page 9, display 2.10: the modulus of the windowed exponential kernel is the
window indicator. -/
private theorem norm_window_kernel512 (h : ℝ) (n : ℤ) (u : ℝ) :
    ‖{u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
        (fun u : ℝ => @fourier 1 n (u : AddCircle (1 : ℝ))) u‖ =
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) u := by
  by_cases hu : u ∈ {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}
  · rw [indicator_of_mem hu, indicator_of_mem hu, norm_fourier512]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, norm_zero]

/-- P0069 page 9, display 2.10: lower bound for the Fourier coefficient of the window
kernel at an integer frequency k with |k| at most B, from cos x ≥ 1 - x^2 / 2
integrated over the window. -/
private theorem kernel_lower512 (h B : ℝ) (hh0 : 0 < h) (k : ℤ) (hk : |(k : ℝ)| ≤ B) :
    2 * h * (1 - (2 * Real.pi * B * h) ^ 2 / 6) ≤
      ‖∫ u in Ioo (-h) h, @fourier 1 k (u : AddCircle (1 : ℝ))‖ := by
  have hint : Integrable (fun u : ℝ => @fourier 1 k (u : AddCircle (1 : ℝ)))
      (volume.restrict (Ioo (-h) h)) :=
    ((continuous_fourier512 k).integrableOn_Icc (a := -h) (b := h)).mono_set
      Ioo_subset_Icc_self
  have hre : (∫ u in Ioo (-h) h, @fourier 1 k (u : AddCircle (1 : ℝ))).re =
      ∫ u in Ioo (-h) h, Real.cos (2 * Real.pi * k * u) := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Complex.reCLM_apply]
    rw [fourier_coe_apply, show (2 * Real.pi * Complex.I * k * u / (1 : ℝ) : ℂ) =
      ((2 * Real.pi * k * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  have hc1 : Continuous (fun u : ℝ => 1 - (2 * Real.pi * B) ^ 2 / 2 * u ^ 2) := by
    fun_prop
  have hc2 : Continuous (fun u : ℝ => Real.cos (2 * Real.pi * k * u)) := by
    fun_prop
  have hk2 : (k : ℝ) ^ 2 ≤ B ^ 2 := sq_le_sq' (abs_le.mp hk).1 (abs_le.mp hk).2
  have hlow : (∫ u in Ioo (-h) h, (1 - (2 * Real.pi * B) ^ 2 / 2 * u ^ 2)) ≤
      ∫ u in Ioo (-h) h, Real.cos (2 * Real.pi * k * u) := by
    apply setIntegral_mono_on
      ((hc1.integrableOn_Icc (a := -h) (b := h)).mono_set Ioo_subset_Icc_self)
      ((hc2.integrableOn_Icc (a := -h) (b := h)).mono_set Ioo_subset_Icc_self)
      measurableSet_Ioo
    intro u _
    have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * k * u)
    have h2 := mul_nonneg (sub_nonneg.mpr hk2) (sq_nonneg (Real.pi * u))
    nlinarith
  have hval : (∫ u in Ioo (-h) h, (1 - (2 * Real.pi * B) ^ 2 / 2 * u ^ 2)) =
      2 * h * (1 - (2 * Real.pi * B * h) ^ 2 / 6) := by
    have i1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-h) h :=
      intervalIntegrable_const
    have i2 : IntervalIntegrable (fun u : ℝ => (2 * Real.pi * B) ^ 2 / 2 * u ^ 2)
        volume (-h) h :=
      (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow]
    simp only [smul_eq_mul]
    norm_num
    ring
  calc 2 * h * (1 - (2 * Real.pi * B * h) ^ 2 / 6)
      = ∫ u in Ioo (-h) h, (1 - (2 * Real.pi * B) ^ 2 / 2 * u ^ 2) := hval.symm
    _ ≤ ∫ u in Ioo (-h) h, Real.cos (2 * Real.pi * k * u) := hlow
    _ = (∫ u in Ioo (-h) h, @fourier 1 k (u : AddCircle (1 : ℝ))).re := hre.symm
    _ ≤ ‖∫ u in Ioo (-h) h, @fourier 1 k (u : AddCircle (1 : ℝ))‖ := Complex.re_le_norm _

/-- P0069 page 9, display 2.10: the Fourier coefficient at n of the windowed
convolution of F restricted to m is the coefficient of F times the coefficient of the
window kernel. -/
private theorem coefficient512 (c h : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 4) (m : Set ℝ)
    (hmc : m ⊆ Ioc c (c + 1)) (F : ℝ → ℂ) (hF : StronglyMeasurable F) (CF : ℝ)
    (hFb : ∀ t, ‖F t‖ ≤ CF) (N₁ n : ℤ) :
    (∫ α in Ioc c (c + 1),
        (∫ t in m, F t * {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
          (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) (α - t)) *
          @fourier 1 (-n) (α : AddCircle (1 : ℝ))) =
      (∫ t in m, F t * @fourier 1 (-n) (t : AddCircle (1 : ℝ))) *
        ∫ u in Ioo (-h) h, @fourier 1 (N₁ - n) (u : AddCircle (1 : ℝ)) := by
  have hg : StronglyMeasurable (fun u : ℝ =>
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
        (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) u *
          @fourier 1 (-n) (u : AddCircle (1 : ℝ))) :=
    ((continuous_fourier512 N₁).stronglyMeasurable.indicator (measurableSet_window512 h)).mul
      (continuous_fourier512 _).stronglyMeasurable
  have hgb : ∀ u : ℝ, ‖{u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
        (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) u *
          @fourier 1 (-n) (u : AddCircle (1 : ℝ))‖ ≤ 1 := fun u => by
    rw [norm_mul, norm_fourier512, mul_one, norm_window_kernel512]
    exact ind_le_one512 _ u
  have hper : Function.Periodic (fun u : ℝ =>
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
        (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) u *
          @fourier 1 (-n) (u : AddCircle (1 : ℝ))) 1 :=
    (window_indicator_periodic512 h _ (fourier_periodic512 N₁)).mul (fourier_periodic512 (-n))
  have key := (fubini_kernel512 c m hmc
    (fun t => F t * @fourier 1 (-n) (t : AddCircle (1 : ℝ))) _
    (hF.mul (continuous_fourier512 _).stronglyMeasurable) hg CF 1
    (fun t => by rw [norm_mul, norm_fourier512, mul_one]; exact hFb t) hgb hper).2
  have e1 : ∀ α : ℝ, (∫ t in m, F t * {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
          (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) (α - t)) *
          @fourier 1 (-n) (α : AddCircle (1 : ℝ)) =
      ∫ t in m, (F t * @fourier 1 (-n) (t : AddCircle (1 : ℝ))) *
        ({u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
          (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) (α - t) *
            @fourier 1 (-n) ((α - t : ℝ) : AddCircle (1 : ℝ))) := by
    intro α
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [fourier_shift512 (-n) α t]
    ring
  simp_rw [e1]
  refine key.trans ?_
  congr 1
  have e2 : ∀ u : ℝ, {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
        (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) u *
          @fourier 1 (-n) (u : AddCircle (1 : ℝ)) =
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
        (fun u : ℝ => @fourier 1 (N₁ - n) (u : AddCircle (1 : ℝ))) u := by
    intro u
    by_cases hu : u ∈ {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}
    · rw [indicator_of_mem hu, indicator_of_mem hu, sub_eq_add_neg, fourier_add]
    · rw [indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]
  simp_rw [e2]
  exact window_integral512 h hh0 hh _

/-- P0069 page 9, the step from 2.10 to 2.11: integrating the windowed energy of a
bounded function over one period of window centres returns 2 h times its energy. -/
private theorem window_mass512 (c h : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 4) (ρ : ℝ → ℝ)
    (hρ : StronglyMeasurable ρ) (Cρ : ℝ) (hρb : ∀ t, ‖ρ t‖ ≤ Cρ) :
    Integrable (fun α => ∫ t in Ioc c (c + 1), ρ t *
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t))
      (volume.restrict (Ioc c (c + 1))) ∧
    (∫ α in Ioc c (c + 1), ∫ t in Ioc c (c + 1), ρ t *
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) =
      (∫ t in Ioc c (c + 1), ρ t) * (2 * h) := by
  have key := fubini_kernel512 c (Ioc c (c + 1)) Subset.rfl ρ
    ({u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ))) hρ
    (stronglyMeasurable_const.indicator (measurableSet_window512 h)) Cρ 1 hρb
    (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ind_nonneg512 _ u)]
      exact ind_le_one512 _ u)
    (window_indicator_periodic512 h _ fun u => rfl)
  refine ⟨key.1, key.2.trans ?_⟩
  congr 1
  rw [window_integral512 h hh0 hh, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- P0069 page 9, display 2.10: the energy of the second polynomial on the part of m
seen through the periodic window centred at α is at most three times the uniform local
energy bound, one term for each of the integer shifts -1, 0, 1. -/
private theorem local_energy512 (c h H E : ℝ) (hh : h ≤ 1 / 4) (hhH : h ≤ 1 / H)
    (m : Set ℝ) (hm : MeasurableSet m) (hmc : m ⊆ Ioc c (c + 1)) (ρ : ℝ → ℝ)
    (hρc : Continuous ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (Cρ : ℝ) (hρb : ∀ t, ρ t ≤ Cρ)
    (hE : ∀ ζ : ℝ, ∫ t in Ioo (ζ - 1 / H) (ζ + 1 / H) ∩ m, ρ t ≤ E) (α : ℝ)
    (hα : α ∈ Ioc c (c + 1)) :
    ∫ t in m, ρ t *
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t) ≤
      3 * E := by
  have hfin : IsFiniteMeasure (volume.restrict m) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono hmc) measure_Ioc_lt_top⟩
  have hρm : IntegrableOn ρ m :=
    (hρc.integrableOn_Icc (a := c) (b := c + 1)).mono_set (hmc.trans Ioc_subset_Icc_self)
  have hind : ∀ ζ : ℝ, IntegrableOn ((Ioo (ζ - 1 / H) (ζ + 1 / H)).indicator ρ) m :=
    fun ζ => hρm.indicator measurableSet_Ioo
  have hwm : Measurable (fun t : ℝ =>
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) :=
    (measurable_const.indicator (measurableSet_window512 h)).comp
      (measurable_const.sub measurable_id)
  have hlhs : IntegrableOn (fun t => ρ t *
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) m :=
    integrable_of_bound512 (hρc.aestronglyMeasurable.mul hwm.aestronglyMeasurable) Cρ
      fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 t) (ind_nonneg512 _ _))]
        calc ρ t * _ ≤ ρ t * 1 :=
              mul_le_mul_of_nonneg_left (ind_le_one512 _ _) (hρ0 t)
          _ ≤ Cρ := by rw [mul_one]; exact hρb t
  have hpt : ∀ t ∈ m, ρ t *
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t) ≤
      (Ioo (α + 1 - 1 / H) (α + 1 + 1 / H)).indicator ρ t +
        (Ioo (α - 1 / H) (α + 1 / H)).indicator ρ t +
          (Ioo (α - 1 - 1 / H) (α - 1 + 1 / H)).indicator ρ t := by
    intro t ht
    have ht' := hmc ht
    have n1 := indicator_nonneg (s := Ioo (α + 1 - 1 / H) (α + 1 + 1 / H)) (f := ρ)
      (fun x _ => hρ0 x) t
    have n2 := indicator_nonneg (s := Ioo (α - 1 / H) (α + 1 / H)) (f := ρ)
      (fun x _ => hρ0 x) t
    have n3 := indicator_nonneg (s := Ioo (α - 1 - 1 / H) (α - 1 + 1 / H)) (f := ρ)
      (fun x _ => hρ0 x) t
    by_cases hw : α - t ∈ {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}
    · rw [indicator_of_mem hw, mul_one]
      obtain ⟨j, hj⟩ := hw
      rw [abs_lt] at hj
      have hj1 : j < 2 := by
        exact_mod_cast (by linarith [hα.2, ht'.1] : (j : ℝ) < 2)
      have hj2 : -2 < j := by
        exact_mod_cast (by linarith [hα.1, ht'.2] : (-2 : ℝ) < j)
      have hj3 : j = -1 ∨ j = 0 ∨ j = 1 := by omega
      rcases hj3 with rfl | rfl | rfl
      · have hmem : t ∈ Ioo (α + 1 - 1 / H) (α + 1 + 1 / H) := by
          push_cast at hj
          exact ⟨by linarith, by linarith⟩
        rw [indicator_of_mem hmem]
        linarith
      · have hmem : t ∈ Ioo (α - 1 / H) (α + 1 / H) := by
          push_cast at hj
          exact ⟨by linarith, by linarith⟩
        rw [indicator_of_mem hmem]
        linarith
      · have hmem : t ∈ Ioo (α - 1 - 1 / H) (α - 1 + 1 / H) := by
          push_cast at hj
          exact ⟨by linarith, by linarith⟩
        rw [indicator_of_mem hmem]
        linarith
    · rw [indicator_of_notMem hw, mul_zero]
      linarith
  have h12 : IntegrableOn (fun t => (Ioo (α + 1 - 1 / H) (α + 1 + 1 / H)).indicator ρ t +
      (Ioo (α - 1 / H) (α + 1 / H)).indicator ρ t) m :=
    (hind (α + 1)).add (hind α)
  have h3 : IntegrableOn (fun t => (Ioo (α - 1 - 1 / H) (α - 1 + 1 / H)).indicator ρ t) m :=
    hind (α - 1)
  have h123 : IntegrableOn (fun t => (Ioo (α + 1 - 1 / H) (α + 1 + 1 / H)).indicator ρ t +
      (Ioo (α - 1 / H) (α + 1 / H)).indicator ρ t +
        (Ioo (α - 1 - 1 / H) (α - 1 + 1 / H)).indicator ρ t) m := h12.add h3
  have h1' : IntegrableOn (fun t => (Ioo (α + 1 - 1 / H) (α + 1 + 1 / H)).indicator ρ t) m :=
    hind (α + 1)
  have h2' : IntegrableOn (fun t => (Ioo (α - 1 / H) (α + 1 / H)).indicator ρ t) m :=
    hind α
  have hE1 := hE (α + 1)
  have hE2 := hE α
  have hE3 := hE (α - 1)
  calc ∫ t in m, ρ t *
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)
      ≤ ∫ t in m, ((Ioo (α + 1 - 1 / H) (α + 1 + 1 / H)).indicator ρ t +
        (Ioo (α - 1 / H) (α + 1 / H)).indicator ρ t +
          (Ioo (α - 1 - 1 / H) (α - 1 + 1 / H)).indicator ρ t) :=
        setIntegral_mono_on hlhs h123 hm hpt
    _ = (∫ t in m, (Ioo (α + 1 - 1 / H) (α + 1 + 1 / H)).indicator ρ t) +
        (∫ t in m, (Ioo (α - 1 / H) (α + 1 / H)).indicator ρ t) +
          ∫ t in m, (Ioo (α - 1 - 1 / H) (α - 1 + 1 / H)).indicator ρ t := by
        rw [integral_add h12 h3, integral_add h1' h2']
    _ = (∫ t in Ioo (α + 1 - 1 / H) (α + 1 + 1 / H) ∩ m, ρ t) +
        (∫ t in Ioo (α - 1 / H) (α + 1 / H) ∩ m, ρ t) +
          ∫ t in Ioo (α - 1 - 1 / H) (α - 1 + 1 / H) ∩ m, ρ t := by
        rw [setIntegral_indicator measurableSet_Ioo, setIntegral_indicator measurableSet_Ioo,
          setIntegral_indicator measurableSet_Ioo, inter_comm m, inter_comm m, inter_comm m]
    _ ≤ 3 * E := by linarith

/-- P0069 page 9, display 2.10: pointwise Cauchy Schwarz for the windowed convolution.
Its squared modulus at α is at most the windowed energy of the first polynomial times
three times the local energy bound for the second. -/
private theorem pointwise512 (c h H E : ℝ) (hh : h ≤ 1 / 4) (hhH : h ≤ 1 / H)
    (m : Set ℝ) (hm : MeasurableSet m) (hmc : m ⊆ Ioc c (c + 1))
    (P R : ℝ → ℂ) (hPc : Continuous P) (hRc : Continuous R) (CP CR : ℝ)
    (hPb : ∀ t, ‖P t‖ ≤ CP) (hRb : ∀ t, ‖R t‖ ≤ CR)
    (hE : ∀ ζ : ℝ, ∫ t in Ioo (ζ - 1 / H) (ζ + 1 / H) ∩ m, ‖R t‖ ^ 2 ≤ E) (N₁ : ℤ) (α : ℝ)
    (hα : α ∈ Ioc c (c + 1)) :
    ‖∫ t in m, P t * R t * {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
        (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) (α - t)‖ ^ 2 ≤
      (∫ t in Ioc c (c + 1), ‖P t‖ ^ 2 *
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) *
          (3 * E) := by
  have hfin : IsFiniteMeasure (volume.restrict m) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono hmc) measure_Ioc_lt_top⟩
  have hwm : Measurable (fun t : ℝ =>
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) :=
    (measurable_const.indicator (measurableSet_window512 h)).comp
      (measurable_const.sub measurable_id)
  have hCP : 0 ≤ CP := (norm_nonneg _).trans (hPb 0)
  have hnorm : ∀ t : ℝ, ‖P t * R t * {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
        (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) (α - t)‖ =
      (‖P t‖ * {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) *
        (‖R t‖ *
          {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) := by
    intro t
    rw [norm_mul, norm_mul, norm_window_kernel512]
    have hs := ind_sq512 {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h} (α - t)
    linear_combination (-(‖P t‖ * ‖R t‖)) * hs
  have h1 : ‖∫ t in m, P t * R t * {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator
        (fun u : ℝ => @fourier 1 N₁ (u : AddCircle (1 : ℝ))) (α - t)‖ ≤
      ∫ t in m, (‖P t‖ *
          {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) *
        (‖R t‖ *
          {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) :=
    (norm_integral_le_integral_norm _).trans
      (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall hnorm)))
  have h2 := cauchy_schwarz512 (volume.restrict m)
    (fun t => ‖P t‖ *
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t))
    (fun t => ‖R t‖ *
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t))
    (hPc.norm.aestronglyMeasurable.mul hwm.aestronglyMeasurable)
    (hRc.norm.aestronglyMeasurable.mul hwm.aestronglyMeasurable) CP CR
    (fun t => by
      rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (ind_nonneg512 _ _))]
      calc ‖P t‖ * _ ≤ ‖P t‖ * 1 :=
            mul_le_mul_of_nonneg_left (ind_le_one512 _ _) (norm_nonneg _)
        _ ≤ CP := by rw [mul_one]; exact hPb t)
    (fun t => by
      rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (ind_nonneg512 _ _))]
      calc ‖R t‖ * _ ≤ ‖R t‖ * 1 :=
            mul_le_mul_of_nonneg_left (ind_le_one512 _ _) (norm_nonneg _)
        _ ≤ CR := by rw [mul_one]; exact hRb t)
  have e3 : ∀ (Q : ℝ → ℂ) (t : ℝ), (‖Q t‖ *
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) ^ 2 =
      ‖Q t‖ ^ 2 *
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t) :=
    fun Q t => by rw [mul_pow, ind_sq512]
  simp only [e3] at h2
  have h3 : (∫ t in m, ‖P t‖ ^ 2 *
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t)) ≤
      ∫ t in Ioc c (c + 1), ‖P t‖ ^ 2 *
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t) := by
    refine setIntegral_mono_set ?_ (Filter.Eventually.of_forall fun t =>
      mul_nonneg (sq_nonneg _) (ind_nonneg512 _ _)) hmc.eventuallyLE
    exact integrable_of_bound512
      ((hPc.norm.pow 2).aestronglyMeasurable.mul hwm.aestronglyMeasurable) (CP ^ 2)
      fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (ind_nonneg512 _ _))]
        calc ‖P t‖ ^ 2 * _ ≤ ‖P t‖ ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left (ind_le_one512 _ _) (sq_nonneg _)
          _ ≤ CP ^ 2 := by
              rw [mul_one]
              exact pow_le_pow_left₀ (norm_nonneg _) (hPb t) 2
  have h4 := local_energy512 c h H E hh hhH m hm hmc (fun t => ‖R t‖ ^ 2) (hRc.norm.pow 2)
    (fun t => sq_nonneg _) (CR ^ 2) (fun t => pow_le_pow_left₀ (norm_nonneg _) (hRb t) 2)
    hE α hα
  have h5 : 0 ≤ ∫ t in m, ‖P t‖ ^ 2 *
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t) :=
    integral_nonneg fun t => mul_nonneg (sq_nonneg _) (ind_nonneg512 _ _)
  have h6 : 0 ≤ ∫ t in m, ‖R t‖ ^ 2 *
      {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < h}.indicator (fun _ => (1 : ℝ)) (α - t) :=
    integral_nonneg fun t => mul_nonneg (sq_nonneg _) (ind_nonneg512 _ _)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
    (h2.trans (mul_le_mul h3 h4 h6 (h5.trans h3)))

/-- P0069 pages 8 and 9, display 2.10 and the reduction to 2.11, for two bounded
continuous factors P and R with the energy of P over one period equal to A: the kernel
lower bound, Bessel, pointwise Cauchy Schwarz and the window mass identity combine to
the mean square bound over an interval of H frequencies. -/
private theorem gallagher_abstract512 (c : ℝ) (m : Set ℝ) (hm : MeasurableSet m)
    (hmc : m ⊆ Ioc c (c + 1)) (P R : ℝ → ℂ) (hPc : Continuous P) (hRc : Continuous R)
    (CP CR : ℝ) (hPb : ∀ t, ‖P t‖ ≤ CP) (hRb : ∀ t, ‖R t‖ ≤ CR) (A : ℝ)
    (hA : (∫ t in Ioc c (c + 1), ‖P t‖ ^ 2) = A)
    (K : Finset ℕ) (N₀ : ℕ) (H E : ℝ) (hH : 1 ≤ H)
    (hK : ∀ N ∈ K, N₀ ≤ N ∧ (N : ℝ) ≤ N₀ + H)
    (hE : ∀ ζ : ℝ, ∫ t in Ioo (ζ - 1 / H) (ζ + 1 / H) ∩ m, ‖R t‖ ^ 2 ≤ E) :
    ∑ N ∈ K, ‖∫ t in m, P t * R t * @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ^ 2 ≤
      30 * H * A * E := by
  have hH0 : 0 < H := by linarith
  have hh0 : 0 < 1 / (8 * H) := by positivity
  have hh4 : 1 / (8 * H) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hhH : 1 / (8 * H) ≤ 1 / H := one_div_le_one_div_of_le hH0 (by linarith)
  have hE0 : 0 ≤ E := (integral_nonneg fun t => sq_nonneg _).trans (hE 0)
  have hA0 : 0 ≤ A := hA ▸ integral_nonneg fun t => sq_nonneg _
  have hCP : 0 ≤ CP := (norm_nonneg _).trans (hPb 0)
  have hCR : 0 ≤ CR := (norm_nonneg _).trans (hRb 0)
  have hfin : volume m < ⊤ := lt_of_le_of_lt (measure_mono hmc) measure_Ioc_lt_top
  have hFm : StronglyMeasurable (fun t => P t * R t) := (hPc.mul hRc).stronglyMeasurable
  have hFb : ∀ t, ‖P t * R t‖ ≤ CP * CR := fun t => by
    rw [norm_mul]
    exact mul_le_mul (hPb t) (hRb t) (norm_nonneg _) hCP
  have hκb : ∀ u : ℝ, ‖{u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < 1 / (8 * H)}.indicator
      (fun u : ℝ => @fourier 1 ((N₀ : ℤ) + (⌊H / 2⌋₊ : ℤ)) (u : AddCircle (1 : ℝ))) u‖ ≤ 1 :=
    fun u => by
      rw [norm_window_kernel512]
      exact ind_le_one512 _ u
  have hfub := fubini_kernel512 c m hmc (fun t => P t * R t)
    ({u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < 1 / (8 * H)}.indicator
      (fun u : ℝ => @fourier 1 ((N₀ : ℤ) + (⌊H / 2⌋₊ : ℤ)) (u : AddCircle (1 : ℝ))))
    hFm ((continuous_fourier512 _).stronglyMeasurable.indicator (measurableSet_window512 _))
    (CP * CR) 1 hFb hκb (window_indicator_periodic512 _ _ (fourier_periodic512 _))
  set G : ℝ → ℂ := fun α => ∫ t in m, P t * R t *
    {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < 1 / (8 * H)}.indicator
      (fun u : ℝ => @fourier 1 ((N₀ : ℤ) + (⌊H / 2⌋₊ : ℤ)) (u : AddCircle (1 : ℝ))) (α - t)
    with hG
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioc c (c + 1))) :=
    hfub.1.aestronglyMeasurable
  have hGb : ∀ α, ‖G α‖ ≤ CP * CR * volume.real m := fun α =>
    norm_setIntegral_le_of_norm_le_const hfin fun t _ => by
      rw [norm_mul]
      calc ‖P t * R t‖ * _ ≤ CP * CR * 1 :=
            mul_le_mul (hFb t) (hκb _) (norm_nonneg _) (mul_nonneg hCP hCR)
        _ = CP * CR := mul_one _
  have hbes := bessel512 c G hGm _ hGb K
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hLeq : 2 * (1 / (8 * H)) * (1 - (2 * Real.pi * (3 * H / 2) * (1 / (8 * H))) ^ 2 / 6) =
      (1 - 3 * Real.pi ^ 2 / 128) / (4 * H) := by
    field_simp
    ring
  have hq : (3 : ℝ) / 4 ≤ 1 - 3 * Real.pi ^ 2 / 128 := by linarith
  have hLpos : 0 < (1 - 3 * Real.pi ^ 2 / 128) / (4 * H) := by
    apply div_pos <;> linarith
  have hcoef : ∀ N ∈ K, ((1 - 3 * Real.pi ^ 2 / 128) / (4 * H)) ^ 2 *
      ‖∫ t in m, P t * R t * @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ^ 2 ≤
      ‖∫ α in Ioc c (c + 1), G α * @fourier 1 (-(N : ℤ)) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
    intro N hN
    have hid := coefficient512 c (1 / (8 * H)) hh0 hh4 m hmc (fun t => P t * R t) hFm
      (CP * CR) hFb ((N₀ : ℤ) + (⌊H / 2⌋₊ : ℤ)) (N : ℤ)
    have hfl : ((⌊H / 2⌋₊ : ℕ) : ℝ) ≤ H / 2 := Nat.floor_le (by positivity)
    have hfl0 : (0 : ℝ) ≤ ((⌊H / 2⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hN0 : (N₀ : ℝ) ≤ N := by exact_mod_cast (hK N hN).1
    have hk : |((((N₀ : ℤ) + (⌊H / 2⌋₊ : ℤ)) - (N : ℤ) : ℤ) : ℝ)| ≤ 3 * H / 2 := by
      push_cast
      rw [abs_le]
      constructor <;> linarith [(hK N hN).2]
    have hlow := kernel_lower512 (1 / (8 * H)) (3 * H / 2) hh0 _ hk
    rw [hLeq] at hlow
    rw [show (∫ α in Ioc c (c + 1), G α * @fourier 1 (-(N : ℤ)) (α : AddCircle (1 : ℝ))) = _
      from hid, norm_mul, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLpos.le hlow 2) (sq_nonneg _)
  have hpt : ∀ α ∈ Ioc c (c + 1), ‖G α‖ ^ 2 ≤
      (∫ t in Ioc c (c + 1), ‖P t‖ ^ 2 *
        {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < 1 / (8 * H)}.indicator (fun _ => (1 : ℝ)) (α - t)) *
          (3 * E) := fun α hα =>
    pointwise512 c (1 / (8 * H)) H E hh4 hhH m hm hmc P R hPc hRc CP CR hPb hRb hE _ α hα
  have hmass := window_mass512 c (1 / (8 * H)) hh0 hh4 (fun t => ‖P t‖ ^ 2)
    (hPc.norm.pow 2).stronglyMeasurable (CP ^ 2) fun t => by
      rw [Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hPb t) 2
  have hG2 : IntegrableOn (fun α => ‖G α‖ ^ 2) (Ioc c (c + 1)) :=
    integrable_of_bound512 (hGm.norm.pow 2) ((CP * CR * volume.real m) ^ 2) fun α => by
      rw [Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hGb α) 2
  have hint : (∫ α in Ioc c (c + 1), ‖G α‖ ^ 2) ≤ A * (2 * (1 / (8 * H))) * (3 * E) := by
    calc (∫ α in Ioc c (c + 1), ‖G α‖ ^ 2)
        ≤ ∫ α in Ioc c (c + 1), (∫ t in Ioc c (c + 1), ‖P t‖ ^ 2 *
          {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < 1 / (8 * H)}.indicator (fun _ => (1 : ℝ))
            (α - t)) * (3 * E) :=
          setIntegral_mono_on hG2 (hmass.1.mul_const _) measurableSet_Ioc hpt
      _ = (∫ α in Ioc c (c + 1), ∫ t in Ioc c (c + 1), ‖P t‖ ^ 2 *
          {u : ℝ | ∃ j : ℤ, |u - (j : ℝ)| < 1 / (8 * H)}.indicator (fun _ => (1 : ℝ))
            (α - t)) * (3 * E) := integral_mul_const _ _
      _ = A * (2 * (1 / (8 * H))) * (3 * E) := by rw [hmass.2, hA]
  have hsum : ((1 - 3 * Real.pi ^ 2 / 128) / (4 * H)) ^ 2 *
      ∑ N ∈ K, ‖∫ t in m, P t * R t * @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ^ 2 ≤
      A * (2 * (1 / (8 * H))) * (3 * E) := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum hcoef).trans (hbes.trans hint)
  have hS0 : 0 ≤ ∑ N ∈ K,
      ‖∫ t in m, P t * R t * @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg fun N _ => sq_nonneg _
  have h5 : (1 - 3 * Real.pi ^ 2 / 128) ^ 2 *
      ∑ N ∈ K, ‖∫ t in m, P t * R t * @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ^ 2 ≤
      12 * H * A * E := by
    calc (1 - 3 * Real.pi ^ 2 / 128) ^ 2 *
          ∑ N ∈ K, ‖∫ t in m, P t * R t *
            @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ^ 2
        = 16 * H ^ 2 * (((1 - 3 * Real.pi ^ 2 / 128) / (4 * H)) ^ 2 *
          ∑ N ∈ K, ‖∫ t in m, P t * R t *
            @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ^ 2) := by
          field_simp
          ring
      _ ≤ 16 * H ^ 2 * (A * (2 * (1 / (8 * H))) * (3 * E)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 12 * H * A * E := by
          field_simp
          ring
  have h6 : (2 : ℝ) / 5 ≤ (1 - 3 * Real.pi ^ 2 / 128) ^ 2 := by nlinarith
  have h7 := mul_le_mul_of_nonneg_right h6 hS0
  have h8 : 0 ≤ H * A * E := mul_nonneg (mul_nonneg hH0.le hA0) hE0
  linarith

/-- P0069 pages 8 and 9, display 2.10 and the reduction to 2.11: the Gallagher type
window inequality. Bessel on a full period, Cauchy Schwarz and a 1-periodic kernel of
radius `1 / (8 * H)` turn a uniform local energy bound for the second polynomial on
windows of radius `1 / H` inside the measurable set `m` into the mean square bound for
the Fourier coefficients of the product over an interval of `H` frequencies. -/
theorem gallagher_window512
    (c : ℝ) (m : Set ℝ) (hm : MeasurableSet m) (hmc : m ⊆ Set.Ioc c (c + 1))
    (S T : Finset ℕ) (a b : ℕ → ℂ) (K : Finset ℕ) (N₀ : ℕ) (H E : ℝ) (hH : 1 ≤ H)
    (hK : ∀ N ∈ K, N₀ ≤ N ∧ (N : ℝ) ≤ N₀ + H)
    (hE : ∀ ζ : ℝ, ∫ t in Set.Ioo (ζ - 1 / H) (ζ + 1 / H) ∩ m,
        ‖∑ k ∈ T, b k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ ^ 2 ≤ E) :
    ∑ N ∈ K, ‖∫ t in m,
        (∑ k ∈ S, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
          (∑ k ∈ T, b k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
            @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ^ 2 ≤
      30 * H * (∑ k ∈ S, ‖a k‖ ^ 2) * E := by
  have hc : ∀ (U : Finset ℕ) (d : ℕ → ℂ), Continuous (fun t : ℝ =>
      ∑ k ∈ U, d k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) := fun U d =>
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_fourier512 _)
  have hb : ∀ (U : Finset ℕ) (d : ℕ → ℂ) (t : ℝ),
      ‖∑ k ∈ U, d k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ ≤ ∑ k ∈ U, ‖d k‖ :=
    fun U d t => by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, norm_fourier512, mul_one]
  exact gallagher_abstract512 c m hm hmc
    (fun t : ℝ => ∑ k ∈ S, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ)))
    (fun t : ℝ => ∑ k ∈ T, b k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ)))
    (hc S a) (hc T b) _ _ (hb S a) (hb T b) _ (parseval512 S a c) K N₀ H E hH hK hE

end LeanLab.BHP1997.Route512
