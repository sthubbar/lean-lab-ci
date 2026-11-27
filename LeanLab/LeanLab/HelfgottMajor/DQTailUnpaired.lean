import LeanLab.HelfgottMajor.Gaussian123Base
import LeanLab.HelfgottMajor.MainHyps123
import LeanLab.HelfgottMajor.MainTail123

/-!
Design queue Q1, run 20261124T0803Z-14981, 2026-11-24. P0014, Helfgott, Major arcs for
Goldbach's problem, arXiv 1305.2897v4, Lemma 4.5, page 41, displays 4.33 to 4.35.

The sealed step `SplitGaussian123.tail_mass_of_corollary` is NOT shown false, and no
counterexample is known. Its printed proof fails in two places. The pairing of rho with
1 minus rho in display 4.33 needs chi real, since for complex chi the point 1 minus rho is a
zero of the L function of chi bar. Display 4.35 drops the boundary term f of y times g of y
that comes from the Stieltjes summation after display 4.28 on page 38.

This file restates the step so that a prover can reach it zero by zero for every primitive
chi. Each zero above height T, on either side of the real axis, is bounded by Corollary 3.2
at k equal to 0, given as hcor, with no pairing. The two sided envelope sum is then bounded
by a Stieltjes summation against the two sided count, which is twice the one sided book count
of `ZeroCount1623.bookCount` up to twice `ZeroCount1623.bookError`, by
`MainTail123.zero_count_two_sided_of_book`. That gives the factor 2 on the tail integrals and
a boundary term 4 times the envelope at T times bookError at T. The density
`TailIntegral123.countDensity` carries 1 over 4t, which covers the 0.15 over t that the
derivative of bookError contributes. With the factor 4.226 of hcor the restated bound is
8.452 times the two tail integrals plus 16.904 times the envelope at T times bookError at T.

Numeric screen at q equal to 1, T equal to 200, shift 0, using the 204 zeta zeros with
ordinate between 200 and 520: the two sided envelope sum is 9.4286e-14, twice the integral is
9.1853e-14, so the boundary term is needed; the counting bound with boundary is 3.1244e-13,
ratio 0.302. The true two sided Mellin mass is 3.2149e-69 against the restated bound
1.3204e-12.

Status: `two_sided_envelope_count_le` is the one new LEAF, a sorry. The reduction
`tail_mass_bound_unpaired_of_count` is PROVED from it as a hypothesis. The restated step
`tail_mass_bound_unpaired` is assembled from the two.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DQTailUnpaired
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- The two branch envelope of display 3.4 on page 10 at height t, as a sum of its two
branches. The Gaussian branch is absent at shift 0. This is the bound of
`SplitGaussian123.corEnvelope_le`, evaluated at the cut height T for the boundary term. -/
noncomputable def branchEnv (δ t : ℝ) : ℝ :=
  exp (-0.1598 * |t|) + if δ = 0 then 0 else exp (-0.1065 * (|t| / (π * |δ|)) ^ 2)

/-- PROVED. The two branch envelope is nonnegative. -/
theorem branchEnv_nonneg (δ t : ℝ) : 0 ≤ branchEnv δ t := by
  unfold branchEnv
  have h1 := exp_pos (-0.1598 * |t|)
  split_ifs
  · linarith
  · linarith [exp_pos (-0.1065 * (|t| / (π * |δ|)) ^ 2)]

/-- The two branch envelope is continuous. -/
private theorem continuous_branchEnv (δ : ℝ) : Continuous (branchEnv δ) := by
  unfold branchEnv
  split_ifs <;> fun_prop

/-- A negative multiple of the height is a linear exponential decay to zero. -/
private theorem tendsto_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => exp (-c * t)) Filter.atTop (nhds 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
  simpa using h

/-- The Gaussian decay factor tends to zero. -/
private theorem tendsto_exp_neg_sq {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => exp (-c * t ^ 2)) Filter.atTop (nhds 0) := by
  have ht2 : Filter.Tendsto (fun t : ℝ => t ^ 2) Filter.atTop Filter.atTop := by
    have h := tendsto_rpow_atTop (y := 2) (by norm_num : (0:ℝ) < 2)
    simpa using h
  have harg : Filter.Tendsto (fun t : ℝ => -c * t ^ 2) Filter.atTop Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (r := -c) (by linarith) ht2
  exact tendsto_exp_atBot.comp harg

/-- The two branch envelope tends to zero at height infinity. -/
private theorem tendsto_branchEnv_atTop (δ : ℝ) :
    Filter.Tendsto (branchEnv δ) Filter.atTop (nhds 0) := by
  unfold branchEnv
  have h1 : Filter.Tendsto (fun t : ℝ => exp (-0.1598 * |t|)) Filter.atTop (nhds 0) := by
    refine (tendsto_exp_neg_mul (c := 0.1598) (by norm_num)).congr' ?_
    filter_upwards [Filter.eventually_atTop.2 ⟨0, fun x hx => hx⟩] with t ht
    rw [abs_of_nonneg ht]
  by_cases hδ : δ = 0
  · simpa [hδ] using h1
  · have h2 : Filter.Tendsto (fun t : ℝ => exp (-0.1065 * (|t| / (π * |δ|)) ^ 2))
        Filter.atTop (nhds 0) := by
      refine (tendsto_exp_neg_sq (c := 0.1065 / (π * |δ|) ^ 2) (by positivity)).congr' ?_
      filter_upwards [Filter.eventually_atTop.2 ⟨0, fun x hx => hx⟩] with t ht
      show exp (-(0.1065 / (π * |δ|) ^ 2) * t ^ 2) = exp (-0.1065 * (|t| / (π * |δ|)) ^ 2)
      rw [abs_of_nonneg ht]
      congr 1
      field_simp
    simpa [hδ] using h1.add h2

/-- The derivative of the two branch envelope at a positive height. -/
private theorem hasDerivAt_branchEnv {δ t : ℝ} (ht : 0 < t) :
    HasDerivAt (branchEnv δ)
      (-(0.1598 * exp (-0.1598 * t) +
        if δ = 0 then 0 else
          (0.213 / (π * |δ|) ^ 2) * (t * exp (-0.1065 * (t / (π * |δ|)) ^ 2)))) t := by
  have h1 : HasDerivAt (fun s : ℝ => exp (-0.1598 * s)) (-0.1598 * exp (-0.1598 * t)) t := by
    have hlin : HasDerivAt (fun s : ℝ => -0.1598 * s) (-0.1598) t := by
      simpa using (hasDerivAt_id t).const_mul (-0.1598)
    simpa [mul_comm] using hlin.exp
  by_cases hδ : δ = 0
  · subst hδ
    have heq : branchEnv 0 =ᶠ[nhds t] (fun s : ℝ => exp (-0.1598 * s)) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have hsp : (0:ℝ) < s := hs
      simp [branchEnv, abs_of_pos hsp]
    refine (h1.congr_of_eventuallyEq heq).congr_deriv ?_
    simp only [ite_true, add_zero]
    ring
  · have hdiv : HasDerivAt (fun s : ℝ => s / (π * |δ|)) (1 / (π * |δ|)) t := by
      simpa using (hasDerivAt_id t).div_const (π * |δ|)
    have hsq : HasDerivAt (fun s : ℝ => -0.1065 * (s / (π * |δ|)) ^ 2)
        (-0.1065 * (2 * (t / (π * |δ|)) * (1 / (π * |δ|)))) t := by
      have hp := hdiv.pow 2
      have hc := hp.const_mul (-0.1065)
      simpa [mul_comm, mul_assoc, mul_left_comm] using hc
    have h2 := hsq.exp
    have hsum := h1.add h2
    have heq : branchEnv δ =ᶠ[nhds t]
        ((fun s : ℝ => exp (-0.1598 * s)) + fun s => exp (-0.1065 * (s / (π * |δ|)) ^ 2)) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have hsp : (0:ℝ) < s := hs
      simp [branchEnv, abs_of_pos hsp, hδ]
    refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
    simp only [hδ, ite_false]
    field_simp
    ring

/-- The decay rate of the two branch envelope is nonnegative. -/
private theorem envDecay_nonneg (δ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 0.1598 * exp (-0.1598 * t) +
        if δ = 0 then 0 else
          (0.213 / (π * |δ|) ^ 2) * (t * exp (-0.1065 * (t / (π * |δ|)) ^ 2)) := by
  have h1 : 0 ≤ 0.1598 * exp (-0.1598 * t) := by positivity
  by_cases hδ : δ = 0
  · simp only [hδ, ite_true, add_zero]
    exact h1
  · simp only [hδ, ite_false]
    have h2 : 0 ≤ (0.213 / (π * |δ|) ^ 2) *
        (t * exp (-0.1065 * (t / (π * |δ|)) ^ 2)) :=
      mul_nonneg (by positivity) (by positivity)
    linarith

/-- Negating a differentiable function, as a lambda. -/
private theorem hasDerivAt_neg_fun {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => -f y) (-f') x :=
  (Filter.EventuallyEq.hasDerivAt_iff (f₀ := fun y => -f y) (f₁ := -f)
    (Filter.Eventually.of_forall fun y => rfl)).mpr h.neg

/-- The envelope equals the tail integral of its decay rate. -/
private theorem branchEnv_eq_integral {δ u : ℝ} (hu : 0 < u) :
    branchEnv δ u = ∫ s in Set.Ioi u, (0.1598 * exp (-0.1598 * s) +
      if δ = 0 then 0 else
        (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) := by
  have hderiv : ∀ s ∈ Set.Ioi u, HasDerivAt (fun x : ℝ => -branchEnv δ x)
      (0.1598 * exp (-0.1598 * s) +
        if δ = 0 then 0 else
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans hu hs
    simpa only [neg_neg] using hasDerivAt_neg_fun (hasDerivAt_branchEnv (δ := δ) hs0)
  have hcont : ContinuousWithinAt (fun x : ℝ => -branchEnv δ x) (Set.Ici u) u :=
    (continuous_branchEnv δ).neg.continuousWithinAt
  have hnonneg : ∀ s ∈ Set.Ioi u,
      0 ≤ 0.1598 * exp (-0.1598 * s) +
        if δ = 0 then 0 else
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2)) :=
    fun s hs => envDecay_nonneg δ (le_of_lt (lt_trans hu hs))
  have hlim : Filter.Tendsto (fun x : ℝ => -branchEnv δ x) Filter.atTop (nhds 0) := by
    simpa using (tendsto_branchEnv_atTop δ).neg
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg hlim
  rw [h]
  ring

/-- The decay rate of the envelope is integrable on the tail. -/
private theorem integrableOn_envDecay {δ u : ℝ} (hu : 0 < u) :
    MeasureTheory.IntegrableOn (fun s : ℝ => 0.1598 * exp (-0.1598 * s) +
      if δ = 0 then 0 else
        (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) (Set.Ioi u) := by
  have hderiv : ∀ s ∈ Set.Ioi u, HasDerivAt (fun x : ℝ => -branchEnv δ x)
      (0.1598 * exp (-0.1598 * s) +
        if δ = 0 then 0 else
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans hu hs
    simpa only [neg_neg] using hasDerivAt_neg_fun (hasDerivAt_branchEnv (δ := δ) hs0)
  have hcont : ContinuousWithinAt (fun x : ℝ => -branchEnv δ x) (Set.Ici u) u :=
    (continuous_branchEnv δ).neg.continuousWithinAt
  have hnonneg : ∀ s ∈ Set.Ioi u,
      0 ≤ 0.1598 * exp (-0.1598 * s) +
        if δ = 0 then 0 else
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2)) :=
    fun s hs => envDecay_nonneg δ (le_of_lt (lt_trans hu hs))
  have hlim : Filter.Tendsto (fun x : ℝ => -branchEnv δ x) Filter.atTop (nhds 0) := by
    simpa using (tendsto_branchEnv_atTop δ).neg
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg hlim

/-- The book main term has the logarithmic derivative of the count density. -/
private theorem hasDerivAt_bookMain (q : ℕ) [NeZero q] {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => ZeroCount1623.bookMain q t)
      (1 / (2 * π) * Real.log ((q : ℝ) * s / (2 * π))) s := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have harg : HasDerivAt (fun t : ℝ => (q : ℝ) * t / (2 * π * exp 1)) ((q : ℝ) / (2 * π * exp 1)) s := by
    have h := ((hasDerivAt_id s).const_mul (q : ℝ)).div_const (2 * π * exp 1)
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  have hne : (q : ℝ) * s / (2 * π * exp 1) ≠ 0 := by
    have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
    positivity
  have hlog : HasDerivAt (fun t : ℝ => Real.log ((q : ℝ) * t / (2 * π * exp 1))) (1 / s) s := by
    have h := harg.log hne
    have hval : ((q : ℝ) / (2 * π * exp 1)) / ((q : ℝ) * s / (2 * π * exp 1)) = 1 / s := by
      have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
      field_simp
    simpa only [hval] using h
  have hlin : HasDerivAt (fun t : ℝ => t / (2 * π)) (1 / (2 * π)) s :=
    (hasDerivAt_id s).div_const (2 * π)
  have hmul := hlin.mul hlog
  have hlogsplit : Real.log ((q : ℝ) * s / (2 * π * exp 1)) =
      Real.log ((q : ℝ) * s / (2 * π)) - 1 := by
    rw [show (q : ℝ) * s / (2 * π * exp 1) = ((q : ℝ) * s / (2 * π)) / exp 1 by
      rw [div_div], Real.log_div (by positivity) (exp_pos 1).ne', Real.log_exp]
  have hval : (1 / (2 * π)) * Real.log ((q : ℝ) * s / (2 * π * exp 1)) + (s / (2 * π)) * (1 / s)
      = 1 / (2 * π) * Real.log ((q : ℝ) * s / (2 * π)) := by
    rw [hlogsplit]
    field_simp
    ring
  have hfun : ∀ t : ℝ, ZeroCount1623.bookMain q t =
      t / (2 * π) * Real.log ((q : ℝ) * t / (2 * π * exp 1)) := by
    intro t
    unfold ZeroCount1623.bookMain
    ring
  refine (hmul.congr_of_eventuallyEq ?_).congr_deriv hval
  filter_upwards with t
  rw [hfun t]
  simp only [Pi.mul_apply]

/-- The tail main term plus the quarter logarithmic term has the count density as derivative. -/
private theorem hasDerivAt_bookTail (q : ℕ) [NeZero q] {T s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => ZeroCount1623.bookMain q t - ZeroCount1623.bookMain q T +
      (1 / 4) * (Real.log t - Real.log T)) (TailIntegral123.countDensity q s) s := by
  have h1 := hasDerivAt_bookMain (q := q) hs
  have h2 : HasDerivAt (fun t : ℝ => (1 / 4) * (Real.log t - Real.log T)) (1 / (4 * s)) s := by
    have hlog : HasDerivAt (fun t : ℝ => Real.log t - Real.log T) (1 / s) s := by
      simpa using (Real.hasDerivAt_log hs.ne').sub_const (Real.log T)
    have h := hlog.const_mul (1 / 4)
    convert h using 1
    field_simp
  have hsum := (h1.sub_const (ZeroCount1623.bookMain q T)).add h2
  convert hsum using 1
  unfold TailIntegral123.countDensity
  ring

/-- The count density is nonnegative above height one hundred. -/
private theorem countDensity_nonneg {q : ℕ} [NeZero q] {s : ℝ} (hs : 100 ≤ s) :
    0 ≤ TailIntegral123.countDensity q s := by
  unfold TailIntegral123.countDensity
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hpos : (0:ℝ) < (q:ℝ) * s / (2 * π) := by
    have : (0:ℝ) < (q:ℝ) * s := by nlinarith
    positivity
  have hone : (1:ℝ) ≤ (q:ℝ) * s / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pi_lt_four]
  have h1 : 0 ≤ 1 / (2 * π) * Real.log ((q:ℝ) * s / (2 * π)) :=
    mul_nonneg (by positivity) (Real.log_nonneg hone)
  have h2 : 0 ≤ 1 / (4 * s) := by positivity
  linarith

/-- The count density is at most linear in the height. -/
private theorem countDensity_le_linear {q : ℕ} [NeZero q] {s : ℝ} (hs : 1 ≤ s) :
    TailIntegral123.countDensity q s ≤ (2 * (q:ℝ) + 2) * s := by
  unfold TailIntegral123.countDensity
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hs0 : (0:ℝ) < s := by linarith
  have hqs : (0:ℝ) < (q:ℝ) * s := by nlinarith
  have hlog : Real.log ((q:ℝ) * s / (2 * π)) ≤ (q:ℝ) * s := by
    have hpos : (0:ℝ) < (q:ℝ) * s / (2 * π) := by positivity
    have h1 : Real.log ((q:ℝ) * s / (2 * π)) ≤ (q:ℝ) * s / (2 * π) - 1 :=
      Real.log_le_sub_one_of_pos hpos
    have h2 : (q:ℝ) * s / (2 * π) ≤ (q:ℝ) * s := by
      apply div_le_self hqs.le
      nlinarith [pi_gt_three]
    linarith
  have hbound : 1 / (2 * π) * Real.log ((q:ℝ) * s / (2 * π)) ≤ (q:ℝ) * s := by
    have hcoef : (0:ℝ) < 1 / (2 * π) := by positivity
    have hcoef1 : 1 / (2 * π) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [pi_gt_three]
    rcases le_or_gt 0 (Real.log ((q:ℝ) * s / (2 * π))) with h | h
    · calc 1 / (2 * π) * Real.log ((q:ℝ) * s / (2 * π))
          ≤ 1 * ((q:ℝ) * s) := mul_le_mul hcoef1 hlog h (by norm_num)
        _ = (q:ℝ) * s := one_mul _
    · have : 1 / (2 * π) * Real.log ((q:ℝ) * s / (2 * π)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoef.le h.le
      linarith
  have hsecond : 1 / (4 * s) ≤ s := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [hbound, hsecond, hqs]

/-- The book main term is nonnegative above height one. -/
private theorem bookMain_nonneg {q : ℕ} [NeZero q] {t : ℝ} (ht : 100 ≤ t) :
    0 ≤ ZeroCount1623.bookMain q t := by
  unfold ZeroCount1623.bookMain
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  apply mul_nonneg (by positivity)
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  nlinarith [pi_lt_four, Real.exp_one_lt_three, exp_pos 1]

/-- The book main term is at most quadratic in height. -/
private theorem bookMain_le_sq {q : ℕ} [NeZero q] {t : ℝ} (ht : 0 < t) :
    ZeroCount1623.bookMain q t ≤ (q:ℝ) * t^2 := by
  unfold ZeroCount1623.bookMain
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqt : (0:ℝ) < (q:ℝ) * t := by positivity
  have hlogb : Real.log ((q:ℝ) * t / (2 * Real.pi * Real.exp 1)) ≤ (q:ℝ) * t := by
    have hpos : (0:ℝ) < (q:ℝ) * t / (2 * Real.pi * Real.exp 1) := by positivity
    have h1 := Real.log_le_sub_one_of_pos hpos
    have h2 : (q:ℝ) * t / (2 * Real.pi * Real.exp 1) ≤ (q:ℝ) * t := by
      apply div_le_self hqt.le
      nlinarith [pi_gt_three, Real.add_one_le_exp (1:ℝ)]
    linarith
  have hcoef : t / (2 * Real.pi) ≤ t := by
    apply div_le_self ht.le
    nlinarith [pi_gt_three]
  by_cases hlog0 : 0 ≤ Real.log ((q:ℝ) * t / (2 * Real.pi * Real.exp 1))
  · calc t / (2 * Real.pi) * Real.log ((q:ℝ) * t / (2 * Real.pi * Real.exp 1))
        ≤ t * ((q:ℝ) * t) := mul_le_mul hcoef hlogb hlog0 (by linarith)
      _ = (q:ℝ) * t^2 := by ring
  · have : t / (2 * Real.pi) * Real.log ((q:ℝ) * t / (2 * Real.pi * Real.exp 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt (not_le.mp hlog0))
    have : (0:ℝ) < (q:ℝ) * t^2 := by positivity
    linarith

/-- The tail main term together with the quarter logarithm is at most quadratic. -/
private theorem bookTail_abs_le {q : ℕ} [NeZero q] {T s : ℝ} (hT : 100 ≤ T) (hs : T ≤ s) :
    |ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
      (1/4) * (Real.log s - Real.log T)| ≤ (2 * (q:ℝ) + 2) * s^2 := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hT0 : (0:ℝ) < T := by linarith
  have hs0 : (0:ℝ) < s := lt_of_lt_of_le hT0 hs
  have hT100 : 100 ≤ s := le_trans hT hs
  have hbmS0 : 0 ≤ ZeroCount1623.bookMain q s := bookMain_nonneg (q := q) hT100
  have hbmT0 : 0 ≤ ZeroCount1623.bookMain q T := bookMain_nonneg (q := q) hT
  have hbmS : ZeroCount1623.bookMain q s ≤ (q:ℝ) * s^2 := bookMain_le_sq (q := q) hs0
  have hbmT : ZeroCount1623.bookMain q T ≤ (q:ℝ) * s^2 := by
    have h1 := bookMain_le_sq (q := q) hT0
    have h2 : (q:ℝ) * T^2 ≤ (q:ℝ) * s^2 := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    linarith
  have hlogeq : Real.log s - Real.log T = Real.log (s / T) :=
    (Real.log_div hs0.ne' hT0.ne').symm
  have hlog0 : 0 ≤ Real.log (s / T) := Real.log_nonneg (by rw [le_div_iff₀ hT0]; linarith)
  have hlogpart : (1/4) * (Real.log s - Real.log T) ≤ s^2 := by
    rw [hlogeq]
    have h1 : Real.log (s / T) ≤ s / T - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : s / T - 1 ≤ s := by
      have h3 : s / T ≤ s := by
        apply div_le_self hs0.le
        linarith
      linarith
    have h4 : (0:ℝ) ≤ Real.log (s / T) := hlog0
    nlinarith
  have hlogpart0 : 0 ≤ (1/4) * (Real.log s - Real.log T) := by
    rw [hlogeq]; linarith
  rw [abs_le]
  constructor <;> nlinarith [hbmS, hbmT, hlogpart, hlogpart0, hbmS0, hbmT0]

/-- A polynomial times a linear exponential is integrable on the tail. -/
private theorem integrableOn_pow_mul_exp_neg {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t ^ k * exp (-b * t)) (Set.Ioi T) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k:ℝ)) (b := b)
    (by linarith : (-1:ℝ) < (k:ℝ)) (by norm_num : (0:ℝ) < 1) hb
  have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (k:ℝ) * exp (-b * t ^ (1:ℝ)))
      (Set.Ioi T) := h.mono_set (fun x hx => lt_of_le_of_lt hT hx)
  refine h1.congr_fun ?_ measurableSet_Ioi
  intro x hx
  show x ^ (k:ℝ) * exp (-b * x ^ (1:ℝ)) = x ^ k * exp (-b * x)
  rw [Real.rpow_one, Real.rpow_natCast]

/-- A polynomial times a Gaussian is integrable on the tail. -/
private theorem integrableOn_pow_mul_exp_neg_sq {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t ^ k * exp (-c * t ^ 2)) (Set.Ioi T) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := (k:ℝ)) (b := c)
    (by linarith : (-1:ℝ) < (k:ℝ)) (by norm_num : (0:ℝ) < 2) hc
  have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (k:ℝ) * exp (-c * t ^ (2:ℝ)))
      (Set.Ioi T) := h.mono_set (fun x hx => lt_of_le_of_lt hT hx)
  refine h1.congr_fun ?_ measurableSet_Ioi
  intro x hx
  show x ^ (k:ℝ) * exp (-c * x ^ (2:ℝ)) = x ^ k * exp (-c * x ^ 2)
  rw [Real.rpow_two, Real.rpow_natCast]

/-- The linear exponential branch of the envelope weighted by the count density is integrable. -/
private theorem integrableOn_exp_mul_density {q : ℕ} [NeZero q] {T : ℝ} (hT : 100 ≤ T) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => exp (-0.1598 * s) * TailIntegral123.countDensity q s) (Set.Ioi T) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun s : ℝ => (2 * (q:ℝ) + 2) * (s ^ 1 * exp (-0.1598 * s))) (Set.Ioi T) :=
    (integrableOn_pow_mul_exp_neg (b := 0.1598) (by norm_num) (by linarith) 1).const_mul _
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => exp (-0.1598 * s) * TailIntegral123.countDensity q s)
      (MeasureTheory.volume.restrict (Set.Ioi T)) := by
    apply Measurable.aestronglyMeasurable
    unfold TailIntegral123.countDensity
    measurability
  refine MeasureTheory.Integrable.mono hmaj hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
  have hs1 : (1:ℝ) ≤ s := by have hsT : T < s := hs; linarith
  have hs100 : (100:ℝ) ≤ s := by have hsT : T < s := hs; linarith
  have hs0 : (0:ℝ) < s := by linarith
  have hexp0 : 0 < exp (-0.1598 * s) := exp_pos _
  have hcd0 : 0 ≤ TailIntegral123.countDensity q s := countDensity_nonneg hs100
  have hcd := countDensity_le_linear (q := q) hs1
  have hC : (0:ℝ) ≤ 2 * (q:ℝ) + 2 := by positivity
  calc ‖exp (-0.1598 * s) * TailIntegral123.countDensity q s‖
      = exp (-0.1598 * s) * TailIntegral123.countDensity q s := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hexp0.le hcd0)]
    _ ≤ exp (-0.1598 * s) * ((2 * (q:ℝ) + 2) * s) :=
        mul_le_mul_of_nonneg_left hcd hexp0.le
    _ = ‖(2 * (q:ℝ) + 2) * (s ^ 1 * exp (-0.1598 * s))‖ := by
        rw [Real.norm_of_nonneg (by
          have h1 : (0:ℝ) ≤ s ^ 1 := by rw [pow_one]; exact hs0.le
          exact mul_nonneg (by nlinarith) (mul_nonneg h1 (exp_pos _).le))]
        ring

/-- The Gaussian branch of the envelope weighted by the count density is integrable. -/
private theorem integrableOn_gauss_mul_density {q : ℕ} [NeZero q] {δ T : ℝ} (hδ : δ ≠ 0)
    (hT : 100 ≤ T) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => exp (-0.1065 * (s / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q s)
      (Set.Ioi T) := by
  have hc : 0 < 0.1065 / (π * |δ|) ^ 2 := by positivity
  have hmaj : MeasureTheory.IntegrableOn
      (fun s : ℝ => (2 * (q:ℝ) + 2) * (s ^ 1 * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2)))
      (Set.Ioi T) :=
    (integrableOn_pow_mul_exp_neg_sq (c := 0.1065 / (π * |δ|) ^ 2) hc (by linarith) 1).const_mul _
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => exp (-0.1065 * (s / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q s)
      (MeasureTheory.volume.restrict (Set.Ioi T)) := by
    apply Measurable.aestronglyMeasurable
    unfold TailIntegral123.countDensity
    measurability
  refine MeasureTheory.Integrable.mono hmaj hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
  have hs1 : (1:ℝ) ≤ s := by have hsT : T < s := hs; linarith
  have hs100 : (100:ℝ) ≤ s := by have hsT : T < s := hs; linarith
  have hs0 : (0:ℝ) < s := by linarith
  have hexp0 : 0 < exp (-0.1065 * (s / (π * |δ|)) ^ 2) := exp_pos _
  have hcd0 : 0 ≤ TailIntegral123.countDensity q s := countDensity_nonneg hs100
  have hcd := countDensity_le_linear (q := q) hs1
  have hexpeq : exp (-0.1065 * (s / (π * |δ|)) ^ 2) =
      exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2) := by
    congr 1
    field_simp
  calc ‖exp (-0.1065 * (s / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q s‖
      = exp (-0.1065 * (s / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q s := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hexp0.le hcd0)]
    _ ≤ exp (-0.1065 * (s / (π * |δ|)) ^ 2) * ((2 * (q:ℝ) + 2) * s) :=
        mul_le_mul_of_nonneg_left hcd hexp0.le
    _ = (2 * (q:ℝ) + 2) * (s ^ 1 * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2)) := by
        rw [hexpeq]; ring
    _ = ‖(2 * (q:ℝ) + 2) * (s ^ 1 * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2))‖ := by
        rw [Real.norm_of_nonneg (by
          have h1 : (0:ℝ) ≤ s ^ 1 := by rw [pow_one]; exact hs0.le
          exact mul_nonneg (by nlinarith) (mul_nonneg h1 (exp_pos _).le))]

/-- The decay rate of the envelope weighted by the tail main term is integrable. -/
private theorem integrableOn_decay_mul_bookTail {q : ℕ} [NeZero q] {δ T : ℝ} (hT : 100 ≤ T) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (0.1598 * exp (-0.1598 * s) +
          if δ = 0 then 0 else
            (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) *
        (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
          (1/4) * (Real.log s - Real.log T))) (Set.Ioi T) := by
  have hT0 : (0:ℝ) ≤ T := by linarith
  have hC : (0:ℝ) ≤ 2 * (q:ℝ) + 2 := by positivity
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (0.1598 * exp (-0.1598 * s) +
          if δ = 0 then 0 else
            (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) *
        (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
          (1/4) * (Real.log s - Real.log T))) (MeasureTheory.volume.restrict (Set.Ioi T)) := by
    apply Measurable.aestronglyMeasurable
    unfold ZeroCount1623.bookMain
    measurability
  by_cases hδ : δ = 0
  · have hmaj : MeasureTheory.IntegrableOn
        (fun s : ℝ => 0.1598 * (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-0.1598 * s))) (Set.Ioi T) :=
      (integrableOn_pow_mul_exp_neg (b := 0.1598) (by norm_num) hT0 2).const_mul _
    refine MeasureTheory.Integrable.mono hmaj hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := by have hsT : T < s := hs; linarith
    have hV := bookTail_abs_le (q := q) hT hs.le
    have hdecif : (0.1598 * exp (-0.1598 * s) +
        if δ = 0 then 0 else
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2)))
        = 0.1598 * exp (-0.1598 * s) := by simp [hδ]
    have hdec0 : 0 ≤ 0.1598 * exp (-0.1598 * s) := by positivity
    calc ‖(0.1598 * exp (-0.1598 * s) +
          if δ = 0 then 0 else
            (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) *
        (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
          (1/4) * (Real.log s - Real.log T))‖
        = 0.1598 * exp (-0.1598 * s) *
            |ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
              (1/4) * (Real.log s - Real.log T)| := by
          rw [hdecif, Real.norm_eq_abs, abs_mul, abs_of_nonneg hdec0]
      _ ≤ 0.1598 * exp (-0.1598 * s) * ((2 * (q:ℝ) + 2) * s ^ 2) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ = ‖0.1598 * (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-0.1598 * s))‖ := by
          rw [Real.norm_of_nonneg (by
            have h1 : (0:ℝ) ≤ s ^ 2 := sq_nonneg s
            exact mul_nonneg (mul_nonneg (by norm_num) (by nlinarith)) (mul_nonneg h1 (exp_pos _).le))]
          ring
  · have hc : 0 < 0.1065 / (π * |δ|) ^ 2 := by positivity
    have hmaj : MeasureTheory.IntegrableOn
        (fun s : ℝ => 0.1598 * (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-0.1598 * s)) +
          (0.213 / (π * |δ|) ^ 2) * (2 * (q:ℝ) + 2) *
            (s ^ 3 * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2))) (Set.Ioi T) :=
      ((integrableOn_pow_mul_exp_neg (b := 0.1598) (by norm_num) hT0 2).const_mul _).add
        ((integrableOn_pow_mul_exp_neg_sq (c := 0.1065 / (π * |δ|) ^ 2) hc hT0 3).const_mul _)
    refine MeasureTheory.Integrable.mono hmaj hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := by have hsT : T < s := hs; linarith
    have hV := bookTail_abs_le (q := q) hT hs.le
    have hdecif : (0.1598 * exp (-0.1598 * s) +
        if δ = 0 then 0 else
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2)))
        = 0.1598 * exp (-0.1598 * s) +
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2)) := by
      simp [hδ]
    have hdec : 0 ≤ 0.1598 * exp (-0.1598 * s) +
        (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2)) := by
      have h := envDecay_nonneg δ hs0.le
      rwa [hdecif] at h
    have hexpeq : exp (-0.1065 * (s / (π * |δ|)) ^ 2) =
        exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2) := by
      congr 1
      field_simp
    have hstep : (0.1598 * exp (-0.1598 * s) +
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2)))
        = 0.1598 * exp (-0.1598 * s) +
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2)) := by
      rw [hexpeq]
    rw [hdecif]
    calc ‖(0.1598 * exp (-0.1598 * s) +
          (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) *
        (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
          (1/4) * (Real.log s - Real.log T))‖
        = (0.1598 * exp (-0.1598 * s) +
            (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) *
            |ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
              (1/4) * (Real.log s - Real.log T)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdec]
      _ ≤ (0.1598 * exp (-0.1598 * s) +
            (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) *
              ((2 * (q:ℝ) + 2) * s ^ 2) :=
          mul_le_mul_of_nonneg_left hV hdec
      _ = (0.1598 * exp (-0.1598 * s) +
            (0.213 / (π * |δ|) ^ 2) * (s * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2))) *
              ((2 * (q:ℝ) + 2) * s ^ 2) := by rw [hstep]
      _ = ‖0.1598 * (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-0.1598 * s)) +
          (0.213 / (π * |δ|) ^ 2) * (2 * (q:ℝ) + 2) *
            (s ^ 3 * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2))‖ := by
          rw [Real.norm_of_nonneg (by
            have h1 : (0:ℝ) ≤ s ^ 2 := sq_nonneg s
            have h2 : (0:ℝ) ≤ s ^ 3 := by positivity
            exact add_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (by nlinarith)) (mul_nonneg h1 (exp_pos _).le))
              (mul_nonneg (mul_nonneg (by positivity) (by nlinarith))
                (mul_nonneg h2 (exp_pos _).le)))]
          ring

/-- The quadratic weight times a linear exponential decays to zero. -/
private theorem tendsto_sq_mul_exp_neg_mul (b : ℝ) (hb : 0 < b) :
    Filter.Tendsto (fun s : ℝ => s ^ 2 * exp (-b * s)) Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun x : ℝ => x ^ 2 * exp (-x)) Filter.atTop (nhds 0) :=
    tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have harg : Filter.Tendsto (fun s : ℝ => b * s) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hb Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun s : ℝ => (b * s) ^ 2 * exp (-(b * s))) Filter.atTop (nhds 0) :=
    hbase.comp harg
  have hlim : Filter.Tendsto (fun s : ℝ => 1 / b ^ 2 * ((b * s) ^ 2 * exp (-(b * s))))
      Filter.atTop (nhds 0) := by
    have h := hcomp.const_mul (1 / b ^ 2)
    simpa [mul_zero] using h
  refine hlim.congr' ?_
  filter_upwards with s
  have hb0 : b ≠ 0 := hb.ne'
  field_simp

/-- The quadratic weight times a Gaussian decays to zero. -/
private theorem tendsto_sq_mul_exp_neg_mul_sq (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun s : ℝ => s ^ 2 * exp (-c * s ^ 2)) Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun y : ℝ => y * exp (-y)) Filter.atTop (nhds 0) := by
    simpa [pow_one] using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have ht2 : Filter.Tendsto (fun s : ℝ => s ^ 2) Filter.atTop Filter.atTop := by
    have h := tendsto_rpow_atTop (y := 2) (by norm_num : (0:ℝ) < 2)
    simpa using h
  have harg : Filter.Tendsto (fun s : ℝ => c * s ^ 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc ht2
  have hcomp : Filter.Tendsto (fun s : ℝ => (c * s ^ 2) * exp (-(c * s ^ 2)))
      Filter.atTop (nhds 0) := hbase.comp harg
  have heq : (fun s : ℝ => s ^ 2 * exp (-c * s ^ 2)) =
      fun s : ℝ => 1 / c * ((c * s ^ 2) * exp (-(c * s ^ 2))) := by
    funext s
    have hc0 : c ≠ 0 := hc.ne'
    field_simp
  rw [heq]
  simpa [one_div, mul_zero] using hcomp.const_mul (1 / c)

/-- The envelope times the tail main term tends to zero at height infinity. -/
private theorem tendsto_branchEnv_mul_bookTail {q : ℕ} [NeZero q] {δ T : ℝ} (hT : 100 ≤ T) :
    Filter.Tendsto (fun s : ℝ => branchEnv δ s *
      (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
        (1/4) * (Real.log s - Real.log T))) Filter.atTop (nhds 0) := by
  have hC : (0:ℝ) ≤ 2 * (q:ℝ) + 2 := by positivity
  have h1 := tendsto_sq_mul_exp_neg_mul 0.1598 (by norm_num)
  by_cases hδ : δ = 0
  · have hmain : Filter.Tendsto
        (fun s : ℝ => (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-0.1598 * s))) Filter.atTop (nhds 0) := by
      simpa using h1.const_mul (2 * (q:ℝ) + 2)
    refine squeeze_zero_norm' ?_ hmain
    filter_upwards [Filter.eventually_atTop.2 ⟨T, fun x hx => hx⟩] with s hs
    have hs0 : (0:ℝ) < s := by linarith
    have hV := bookTail_abs_le (q := q) hT hs
    have hbE : branchEnv δ s = exp (-0.1598 * s) := by
      unfold branchEnv
      simp [hδ, abs_of_nonneg hs0.le]
    rw [hbE, Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le]
    calc exp (-0.1598 * s) *
          |ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
            (1/4) * (Real.log s - Real.log T)|
        ≤ exp (-0.1598 * s) * ((2 * (q:ℝ) + 2) * s ^ 2) :=
          mul_le_mul_of_nonneg_left hV (exp_pos _).le
      _ = (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-0.1598 * s)) := by ring
  · have hc : 0 < 0.1065 / (π * |δ|) ^ 2 := by positivity
    have h2 := tendsto_sq_mul_exp_neg_mul_sq (0.1065 / (π * |δ|) ^ 2) hc
    have hA : Filter.Tendsto
        (fun s : ℝ => (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-0.1598 * s))) Filter.atTop (nhds 0) := by
      simpa using h1.const_mul (2 * (q:ℝ) + 2)
    have hB : Filter.Tendsto
        (fun s : ℝ => (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2)))
        Filter.atTop (nhds 0) := by
      simpa using h2.const_mul (2 * (q:ℝ) + 2)
    have hmain : Filter.Tendsto
        (fun s : ℝ => (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-0.1598 * s)) +
          (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2)))
        Filter.atTop (nhds 0) := by simpa using hA.add hB
    refine squeeze_zero_norm' ?_ hmain
    filter_upwards [Filter.eventually_atTop.2 ⟨T, fun x hx => hx⟩] with s hs
    have hs0 : (0:ℝ) < s := by linarith
    have hV := bookTail_abs_le (q := q) hT hs
    have hbE : branchEnv δ s = exp (-0.1598 * s) +
        exp (-0.1065 * (s / (π * |δ|)) ^ 2) := by
      unfold branchEnv
      simp [hδ, abs_of_nonneg hs0.le]
    have hexpeq : exp (-0.1065 * (s / (π * |δ|)) ^ 2) =
        exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2) := by
      congr 1
      field_simp
    have hbE0 : 0 ≤ exp (-0.1598 * s) + exp (-0.1065 * (s / (π * |δ|)) ^ 2) := by
      positivity
    rw [hbE, Real.norm_eq_abs, abs_mul, abs_of_nonneg hbE0]
    calc (exp (-0.1598 * s) + exp (-0.1065 * (s / (π * |δ|)) ^ 2)) *
          |ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
            (1/4) * (Real.log s - Real.log T)|
        ≤ (exp (-0.1598 * s) + exp (-0.1065 * (s / (π * |δ|)) ^ 2)) *
            ((2 * (q:ℝ) + 2) * s ^ 2) :=
          mul_le_mul_of_nonneg_left hV hbE0
      _ = (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-0.1598 * s)) +
          (2 * (q:ℝ) + 2) * (s ^ 2 * exp (-(0.1065 / (π * |δ|) ^ 2) * s ^ 2)) := by
          rw [hexpeq]; ring

/-- The two sided count bound is at most twice the tail main term plus the boundary term. -/
private theorem countBound_le_bookTail {q : ℕ} [NeZero q] {T s : ℝ} (hT : 100 ≤ T) (hs : T ≤ s) :
    2 * (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T) +
        2 * (ZeroCount1623.bookError q s + ZeroCount1623.bookError q T) ≤
      2 * (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
          (1/4) * (Real.log s - Real.log T)) + 4 * ZeroCount1623.bookError q T := by
  unfold ZeroCount1623.bookError
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hT0 : (0:ℝ) < T := by linarith
  have hs0 : (0:ℝ) < s := by linarith
  have hlogqs : Real.log ((q:ℝ) * s) = Real.log q + Real.log s := Real.log_mul hq.ne' hs0.ne'
  have hlogqT : Real.log ((q:ℝ) * T) = Real.log q + Real.log T := Real.log_mul hq.ne' hT0.ne'
  have hlog : Real.log T ≤ Real.log s := Real.log_le_log hT0 hs
  rw [hlogqs, hlogqT]
  linarith

/-- The count of the tail zeros up to height `s` is finite. -/
private theorem tail_zeros_cut_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T s : ℝ) :
    {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} | |ρ.val.im| ≤ s}.Finite := by
  classical
  apply ((ZeroCount1623.stripZeros_finite χ s).preimage (f := Subtype.val)
    Subtype.val_injective.injOn).subset
  intro ρ hρ
  exact ⟨ρ.property.1, ρ.property.2.1, ρ.property.2.2.1, hρ⟩

/-- The zeros of the L function of a character in the open strip form a countable set. -/
private theorem strip_zeros_countable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Countable {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} := by
  have hcov : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} ⊆
      ⋃ n : ℕ, (ZeroCount1623.stripZeros χ ((n : ℝ) + 1) : Set ℂ) := by
    intro ρ hρ
    refine Set.mem_iUnion.mpr ⟨⌈|ρ.im|⌉₊, hρ.1, hρ.2.1, hρ.2.2.1, ?_⟩
    have := Nat.le_ceil |ρ.im|
    linarith
  refine Set.Countable.mono hcov ?_
  exact Set.countable_iUnion (fun n => (ZeroCount1623.stripZeros_finite χ ((n : ℝ) + 1)).countable)

/-- Abel summation: the envelope weighted zero sum is the tail integral of the decay rate times the
cut count. -/
private theorem envelope_sum_eq_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 100 ≤ T)
    (hsum : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * branchEnv δ ρ.val.im) =
      ∫ s in Set.Ioi T, (0.1598 * exp (-0.1598 * s) +
          if δ = 0 then 0 else
            (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) *
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            (if |ρ.val.im| ≤ s then 1 else 0)) := by
  classical
  haveI hcount : Countable {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} := strip_zeros_countable χ T
  have hT0 : (0:ℝ) < T := by linarith
  let hfun : ℝ → ℝ := fun s => 0.1598 * exp (-0.1598 * s) +
    if δ = 0 then 0 else (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))
  let F : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} → ℝ → ℝ :=
    fun ρ s => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
      (Set.Ici |ρ.val.im|).indicator hfun s
  have hnn : ∀ (ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}) (s : ℝ), 0 ≤ F ρ s := by
    intro ρ s
    have h1 : 0 ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) :=
      Nat.cast_nonneg _
    by_cases h : s ∈ Set.Ici |ρ.val.im|
    · have hs0 : 0 ≤ s := le_trans (abs_nonneg _) h
      simp only [F, Set.indicator_of_mem h, hfun]
      exact mul_nonneg h1 (envDecay_nonneg δ hs0)
    · simp only [F, Set.indicator_of_notMem h, mul_zero]
      exact le_refl 0
  have hint : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, MeasureTheory.Integrable (F ρ) MeasureTheory.volume := by
    intro ρ
    have hu : 0 < |ρ.val.im| := lt_of_lt_of_le hT0 ρ.property.2.2.2.le
    have hbase : MeasureTheory.IntegrableOn hfun (Set.Ioi |ρ.val.im|) MeasureTheory.volume := by
      have := integrableOn_envDecay (δ := δ) hu
      simpa [hfun] using this
    have h1 : MeasureTheory.IntegrableOn hfun (Set.Ici |ρ.val.im|) MeasureTheory.volume :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mpr hbase
    have hind : MeasureTheory.Integrable ((Set.Ici |ρ.val.im|).indicator hfun) :=
      h1.integrable_indicator measurableSet_Ici
    exact hind.const_mul _
  have hnorm : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
      ∫ s, ‖F ρ s‖ = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        branchEnv δ ρ.val.im := by
    intro ρ
    have hu : 0 < |ρ.val.im| := lt_of_lt_of_le hT0 ρ.property.2.2.2.le
    calc ∫ s, ‖F ρ s‖ = ∫ s, F ρ s := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
          exact Real.norm_of_nonneg (hnn ρ s)
      _ = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ∫ s, (Set.Ici |ρ.val.im|).indicator hfun s := by
          simp only [F]
          rw [MeasureTheory.integral_const_mul]
      _ = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ∫ s in Set.Ici |ρ.val.im|, hfun s := by
          rw [MeasureTheory.integral_indicator measurableSet_Ici]
      _ = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ∫ s in Set.Ioi |ρ.val.im|, hfun s := by
          rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
      _ = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            branchEnv δ ρ.val.im := by
          have hbe := branchEnv_eq_integral (δ := δ) hu
          rw [← hbe]
          congr 1
          simp [branchEnv]
  have hnorm' : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
      ∫ s, F ρ s = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        branchEnv δ ρ.val.im := by
    intro ρ
    rw [← hnorm ρ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    exact (Real.norm_of_nonneg (hnn ρ s)).symm
  have hsumm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => ∫ s, ‖F ρ s‖) := by
    have hfun_eq : (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => ∫ s, ‖F ρ s‖) =
        fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          branchEnv δ ρ.val.im := funext hnorm
    rw [hfun_eq]
    exact hsum
  have hpoint : ∀ s : ℝ, (∑' ρ, F ρ s) =
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (if |ρ.val.im| ≤ s then 1 else 0)) * hfun s := by
    intro s
    let S := (tail_zeros_cut_finite χ T s).toFinset
    have hmem : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, ρ ∈ S ↔ |ρ.val.im| ≤ s := fun ρ =>
      Set.Finite.mem_toFinset _
    have hsupp1 : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, ρ ∉ S → F ρ s = 0 := by
      intro ρ hρ
      have hlt : s ∉ Set.Ici |ρ.val.im| := fun hcon => hρ ((hmem ρ).mpr hcon)
      simp only [F, Set.indicator_of_notMem hlt, mul_zero]
    have hsupp2 : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        ρ ∉ S → (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (if |ρ.val.im| ≤ s then 1 else 0) = 0 := by
      intro ρ hρ
      have hnot : ¬ (|ρ.val.im| ≤ s) := fun hcon => hρ ((hmem ρ).mpr hcon)
      simp [hnot]
    rw [tsum_eq_sum hsupp1, tsum_eq_sum hsupp2, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    have hs : |ρ.val.im| ≤ s := (hmem ρ).mp hρ
    have hmemIci : s ∈ Set.Ici |ρ.val.im| := hs
    have hone : (if |ρ.val.im| ≤ s then (1:ℝ) else 0) = 1 := if_pos hs
    simp only [F, Set.indicator_apply]
    rw [if_pos hmemIci, hone]
    ring
  have hzero : ∀ s ∉ Set.Ioi T, (∑' ρ, F ρ s) = 0 := by
    intro s hs
    have hsT : s ≤ T := le_of_not_gt hs
    have hfun0 : (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => F ρ s) = fun _ => 0 := by
      funext ρ
      have hγ : T < |ρ.val.im| := ρ.property.2.2.2
      have hlt : s ∉ Set.Ici |ρ.val.im| := fun hcon =>
        absurd hcon (not_le.mpr (lt_of_le_of_lt hsT hγ))
      simp only [F, Set.indicator_of_notMem hlt, mul_zero]
    rw [hfun0, tsum_zero]
  have key := MeasureTheory.integral_tsum_of_summable_integral_norm (F := F) hint hsumm
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * branchEnv δ ρ.val.im)
      = ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, ∫ s, F ρ s :=
        tsum_congr (fun ρ => (hnorm' ρ).symm)
    _ = ∫ s, ∑' ρ, F ρ s := key
    _ = ∫ s, (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            (if |ρ.val.im| ≤ s then 1 else 0)) * hfun s := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
        exact hpoint s
    _ = ∫ s in Set.Ioi T, (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            (if |ρ.val.im| ≤ s then 1 else 0)) * hfun s := by
        refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
        intro s hs
        have hs' : s ∉ Set.Ioi T := hs
        have hzero2 : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
              (if |ρ.val.im| ≤ s then 1 else 0)) = 0 := by
          have hfun0 : (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                (if |ρ.val.im| ≤ s then 1 else 0)) = fun _ => 0 := by
            funext ρ
            have hγ : T < |ρ.val.im| := ρ.property.2.2.2
            have hsT : s ≤ T := le_of_not_gt hs
            have hle : ¬ (|ρ.val.im| ≤ s) := fun hcon => absurd hcon (not_le.mpr (lt_of_le_of_lt hsT hγ))
            simp [hle]
          rw [hfun0, tsum_zero]
        rw [hzero2, zero_mul]
    _ = ∫ s in Set.Ioi T, (0.1598 * exp (-0.1598 * s) +
          if δ = 0 then 0 else
            (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))) *
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            (if |ρ.val.im| ≤ s then 1 else 0)) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
        simp only [hfun]
        ring

/-- The `s`-strip filtered at height `T` is the `T`-strip, for `T ≤ s`. -/
private theorem stripZeros_filter_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {T s : ℝ} (hTs : T ≤ s) :
    (ZeroCount1623.stripZeros_finite χ s).toFinset.filter (fun ρ => |ρ.im| ≤ T) =
      (ZeroCount1623.stripZeros_finite χ T).toFinset := by
  apply Finset.ext
  intro ρ
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, ZeroCount1623.stripZeros]
  constructor
  · rintro ⟨⟨h1, h2, h3, -⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3, h4.trans hTs⟩, h4⟩

/-- The two sided envelope count above height `T`, cut at height `s`, is the finset difference of
the strip counts. -/
private theorem count_indicator_eq_band {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {T s : ℝ} (hTs : T ≤ s) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (if |ρ.val.im| ≤ s then 1 else 0)) =
      (∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ s).toFinset,
          (ZeroCount1623.mult χ ρ : ℝ)) -
        (∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ T).toFinset,
          (ZeroCount1623.mult χ ρ : ℝ)) := by
  classical
  set I := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} with hI
  set A := (ZeroCount1623.stripZeros_finite χ s).toFinset with hA
  set B := (ZeroCount1623.stripZeros_finite χ T).toFinset with hB'
  have hmemA : ∀ x : ℂ, x ∈ A ↔ DirichletCharacter.LFunction χ x = 0 ∧ 0 < x.re ∧ x.re < 1 ∧ |x.im| ≤ s := by
    intro x; rw [hA]; simp [ZeroCount1623.stripZeros]
  have hmemB : ∀ x : ℂ, x ∈ B ↔ DirichletCharacter.LFunction χ x = 0 ∧ 0 < x.re ∧ x.re < 1 ∧ |x.im| ≤ T := by
    intro x; rw [hB']; simp [ZeroCount1623.stripZeros]
  haveI : Finite {ρ : I // |ρ.val.im| ≤ s} :=
    Finite.of_injective
      (fun ρ : {ρ : I // |ρ.val.im| ≤ s} =>
        (⟨ρ.val.val, ρ.val.property.1, ρ.val.property.2.1, ρ.val.property.2.2.1,
          ρ.property⟩ : ZeroCount1623.ZeroIdx χ s))
      (fun a b h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  haveI : Fintype {ρ : I // |ρ.val.im| ≤ s} := Fintype.ofFinite _
  have hind : ∀ ρ : I, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (if |ρ.val.im| ≤ s then 1 else 0) =
      {ρ : I | |ρ.val.im| ≤ s}.indicator
        (fun ρ : I => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ρ := by
    intro ρ
    by_cases h : |ρ.val.im| ≤ s <;> simp [Set.indicator, h]
  have hstep : (∑' ρ : I, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (if |ρ.val.im| ≤ s then 1 else 0)) =
      ∑' ρ : {ρ : I // |ρ.val.im| ≤ s},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ) :=
    (tsum_congr hind).trans (tsum_subtype {ρ : I | |ρ.val.im| ≤ s}
      (fun ρ : I => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ))).symm
  rw [hstep, tsum_fintype]
  let ψ : {ρ : I // |ρ.val.im| ≤ s} → {x : ℂ // x ∈ A \ B} := fun ρ =>
    ⟨ρ.val.val, by
      have h1 : ρ.val.val ∈ A := (hmemA _).mpr ⟨ρ.val.property.1, ρ.val.property.2.1,
        ρ.val.property.2.2.1, ρ.property⟩
      have h2 : ρ.val.val ∉ B := by
        intro hcon
        exact absurd ((hmemB _).mp hcon).2.2.2 (not_le.mpr ρ.val.property.2.2.2)
      exact Finset.mem_sdiff.mpr ⟨h1, h2⟩⟩
  have hψ : Function.Bijective ψ := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      have h' : a.val.val = b.val.val := congrArg (fun z => z.val) hab
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨x, hx⟩
      obtain ⟨hxA, hxB⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨h1, h2, h3, h4⟩ := (hmemA x).mp hxA
      have hxT : T < |x.im| := by
        by_contra hcon
        exact hxB ((hmemB x).mpr ⟨h1, h2, h3, not_lt.mp hcon⟩)
      refine ⟨⟨⟨x, h1, h2, h3, hxT⟩, h4⟩, ?_⟩
      exact Subtype.ext rfl
  have hbij := Fintype.sum_bijective ψ hψ
      (fun ρ : {ρ : I // |ρ.val.im| ≤ s} =>
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ))
      (fun x : {x : ℂ // x ∈ A \ B} => (ZeroCount1623.mult χ x.val : ℝ))
      (fun ρ => rfl)
  have hcoe : (∑ x : {x : ℂ // x ∈ A \ B}, (ZeroCount1623.mult χ x.val : ℝ)) =
      ∑ x ∈ A \ B, (ZeroCount1623.mult χ x : ℝ) :=
    Finset.sum_coe_sort (A \ B) (fun x : ℂ => (ZeroCount1623.mult χ x : ℝ))
  rw [hbij, hcoe]
  have hBA : B ⊆ A := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := (hmemB x).mp hx
    exact (hmemA x).mpr ⟨h1, h2, h3, h4.trans hTs⟩
  have hsdiff := Finset.sum_sdiff hBA (f := fun ρ => (ZeroCount1623.mult χ ρ : ℝ))
  linarith [hsdiff]

/-- The pointwise upper bound for the cut two sided count, from the book zero count. -/
private theorem count_indicator_le (hB : MainHyps123.BookZeroCount) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T s : ℝ} (hT : 1 ≤ T) (hTs : T ≤ s) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (if |ρ.val.im| ≤ s then 1 else 0)) ≤
      2 * (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T) +
        2 * (ZeroCount1623.bookError q s + ZeroCount1623.bookError q T) := by
  have hs1 : 1 ≤ s := hT.trans hTs
  have hs := MainTail123.zero_count_two_sided_of_book hB χ hχ hs1
  have htt := MainTail123.zero_count_two_sided_of_book hB χ hχ hT
  rw [count_indicator_eq_band χ hTs]
  have h1 := (abs_le.mp hs).2
  have h2 := (abs_le.mp htt).1
  linarith [h1, h2]

/-- The cut zero count is a measurable function of the height. -/
private theorem measurable_tailCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Measurable (fun s : ℝ => ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (if |ρ.val.im| ≤ s then 1 else 0)) := by
  classical
  have hsumm : ∀ s : ℝ, Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (if |ρ.val.im| ≤ s then 1 else 0)) := by
    intro s
    refine summable_of_ne_finset_zero (s := (tail_zeros_cut_finite χ T s).toFinset) ?_
    intro ρ hρ
    have hnot : ¬ (|ρ.val.im| ≤ s) := fun hc => hρ ((Set.Finite.mem_toFinset _).mpr hc)
    simp [hnot]
  have hmono : Monotone (fun s : ℝ => ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (if |ρ.val.im| ≤ s then 1 else 0)) := by
    intro s t hst
    refine (hsumm s).tsum_le_tsum (fun ρ => ?_) (hsumm t)
    have hnn : 0 ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) :=
      Nat.cast_nonneg _
    refine mul_le_mul_of_nonneg_left ?_ hnn
    by_cases h : |ρ.val.im| ≤ s
    · have h2 : |ρ.val.im| ≤ t := le_trans h hst
      simp [h, h2]
    · have h2 : (0:ℝ) ≤ (if |ρ.val.im| ≤ t then 1 else 0) := by
        split_ifs <;> norm_num
      simp [h]
      exact h2
  exact hmono.measurable

/-- LEAF: OPEN. The counting step of P0014 Lemma 4.5 on page 41, displays 4.33 to 4.35, done
without the pairing of display 4.33 and with the boundary term that page 38 drops.
CONDITIONAL ON hB, the book zero count of display 4.26 on page 38 in the one sided half
weighted form of book page 431. The sum over all zeros of the L function of chi above
height T on both sides, each weighted by its multiplicity times the two branch envelope, is
at most twice the two tail integrals plus 4 times the envelope at T times bookError at T.
Proof route: the two sided count N of t is within twice bookError of twice bookMain for t at
least 1. Stieltjes summation of the decreasing envelope f gives the sum as minus f of T
times N of T minus the integral of f prime times N. Bound N of T from below and N of t from
above, then integrate the error part by parts: the derivative of bookMain is the log part of
countDensity and the derivative of bookError is 0.15 over t, below the 1 over 4t of
countDensity. The two boundary pieces give 4 times f of T times bookError of T.
Numeric screen at q equal to 1, T equal to 200, shift 0: left side 9.4286e-14, right side
3.1244e-13.
STUCK note, three approaches scoped in this run, none finished in the time box. First,
Mathlib Abel summation `sum_mul_eq_sub_integral_mul` is indexed by natural numbers, while the
zero ordinates are real, so it does not apply without a change of index. Second, the unit
shell split of `tail_envelope_summable_of_shell_count` bounds each shell by its lower end
height, which costs a factor exp of 0.1598 per shell and does not reach the constant 2.
Third, the route that should work: for each zero write f of gamma minus f of U as the
integral of minus f prime from gamma to U, swap the finite sum with the integral via
`MeasureTheory.integral_finset_sum`, which turns it into the integral of minus f prime times
N of t minus N of T, apply `MainTail123.zero_count_two_sided_of_book` pointwise, and let U go
to infinity by monotone convergence. It needs the derivative bounds of both branches and the
integrability already proved in TailIntegral123. Estimated a few hundred lines. -/
theorem two_sided_envelope_count_le (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) ≤
      2 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      4 * branchEnv δ T * ZeroCount1623.bookError q T := by
  classical
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hsum : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) :=
    tail_envelope_summable_of_shell_count χ δ T (2 * (q:ℝ) + 18) hT1
      (MainTail123.tail_shell_count_le_quadratic_of_book hB χ hχ T)
  set hfun : ℝ → ℝ := fun s => 0.1598 * exp (-0.1598 * s) +
    if δ = 0 then 0 else (0.213 / (π * |δ|) ^ 2) * (s * exp (-0.1065 * (s / (π * |δ|)) ^ 2))
    with hhfun
  set V : ℝ → ℝ := fun s => ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
    (1/4) * (Real.log s - Real.log T) with hV
  set c : ℝ := ZeroCount1623.bookError q T with hc
  set Nind : ℝ → ℝ := fun s => ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
      (if |ρ.val.im| ≤ s then 1 else 0) with hNind
  have habel : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) =
      ∫ s in Set.Ioi T, hfun s * Nind s := by
    have h1 := envelope_sum_eq_integral (q := q) χ δ T hT100 hsum
    rw [show (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            (exp (-0.1598 * |ρ.val.im|) +
              if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) =
        ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * branchEnv δ ρ.val.im
        from tsum_congr (fun ρ => by simp [branchEnv])]
    exact h1
  have hfun_nn : ∀ s ∈ Set.Ioi T, 0 ≤ hfun s := by
    intro s hs
    have hs0 : (0:ℝ) < s := lt_of_lt_of_le hT0 hs.le
    have h := envDecay_nonneg δ hs0.le
    simpa [hhfun] using h
  have hint_h : MeasureTheory.IntegrableOn hfun (Set.Ioi T) MeasureTheory.volume := by
    have := integrableOn_envDecay (δ := δ) hT0
    simpa [hhfun] using this
  have hint_hV : MeasureTheory.IntegrableOn (fun s => hfun s * V s) (Set.Ioi T)
      MeasureTheory.volume := by
    have := integrableOn_decay_mul_bookTail (q := q) (δ := δ) hT100
    simpa [hhfun, hV] using this
  have hint_hB : MeasureTheory.IntegrableOn (fun s => hfun s * (2 * V s + 4 * c))
      (Set.Ioi T) MeasureTheory.volume := by
    have h2 : MeasureTheory.IntegrableOn (fun s => 2 * (hfun s * V s) + (4 * c) * hfun s)
        (Set.Ioi T) MeasureTheory.volume :=
      ((hint_hV.const_mul 2).add (hint_h.const_mul (4 * c)))
    refine h2.congr_fun (fun s hs => ?_) measurableSet_Ioi
    ring
  have hNle : ∀ s ∈ Set.Ioi T, Nind s ≤ 2 * V s + 4 * c := by
    intro s hs
    have hsT : T ≤ s := hs.le
    have h1 := count_indicator_le hB χ hχ hT1 hsT
    have h2 := countBound_le_bookTail (q := q) hT100 hsT
    have h2' : 2 * (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T) +
        2 * (ZeroCount1623.bookError q s + ZeroCount1623.bookError q T)
        ≤ 2 * V s + 4 * c := by
      have hval : 2 * V s + 4 * c = 2 * (ZeroCount1623.bookMain q s - ZeroCount1623.bookMain q T +
          (1/4) * (Real.log s - Real.log T)) + 4 * ZeroCount1623.bookError q T := by
        simp only [hV, hc]
      rw [hval]
      exact h2
    exact le_trans h1 h2'
  have hNmeas : Measurable Nind := measurable_tailCount (q := q) χ T
  have hfun_meas : Measurable hfun := by
    simp only [hhfun]
    measurability
  have hint_hN : MeasureTheory.IntegrableOn (fun s => hfun s * Nind s) (Set.Ioi T)
      MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono hint_hB (hfun_meas.mul hNmeas).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hh0 : 0 ≤ hfun s := hfun_nn s hs
    have hle := hNle s hs
    have hN0 : 0 ≤ Nind s := by
      refine tsum_nonneg (fun ρ => ?_)
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      split_ifs <;> norm_num
    have hB0 : 0 ≤ 2 * V s + 4 * c := le_trans hN0 hle
    rw [Real.norm_of_nonneg (mul_nonneg hh0 hN0),
      Real.norm_of_nonneg (mul_nonneg hh0 hB0)]
    exact mul_le_mul_of_nonneg_left hle hh0
  have hstep1 : ∫ s in Set.Ioi T, hfun s * Nind s ≤ ∫ s in Set.Ioi T, hfun s * (2 * V s + 4 * c) := by
    refine MeasureTheory.integral_mono_ae hint_hN hint_hB ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_le_mul_of_nonneg_left (hNle s hs) (hfun_nn s hs)
  have hstep2 : ∫ s in Set.Ioi T, hfun s * (2 * V s + 4 * c) =
      2 * (∫ s in Set.Ioi T, hfun s * V s) + 4 * c * ∫ s in Set.Ioi T, hfun s := by
    have hcongr : (fun s => hfun s * (2 * V s + 4 * c)) =
        fun s => 2 * (hfun s * V s) + (4 * c) * hfun s := funext (fun s => by ring)
    rw [hcongr, MeasureTheory.integral_add (hint_hV.const_mul 2) (hint_h.const_mul (4 * c)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hint_uv' : MeasureTheory.IntegrableOn
      (fun s => branchEnv δ s * TailIntegral123.countDensity q s)
      (Set.Ioi T) MeasureTheory.volume := by
    by_cases hδ : δ = 0
    · have h1 := integrableOn_exp_mul_density (q := q) hT100
      refine h1.congr_fun (fun s hs => ?_) measurableSet_Ioi
      have hs0 : (0:ℝ) < s := lt_of_lt_of_le hT0 hs.le
      have hbE : branchEnv δ s = exp (-0.1598 * s) := by
        simp [branchEnv, hδ, abs_of_pos hs0]
      show exp (-0.1598 * s) * TailIntegral123.countDensity q s =
        branchEnv δ s * TailIntegral123.countDensity q s
      rw [hbE]
    · have hsplit : MeasureTheory.IntegrableOn
          (fun s => exp (-0.1598 * s) * TailIntegral123.countDensity q s +
            exp (-0.1065 * (s / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q s)
          (Set.Ioi T) MeasureTheory.volume :=
        (integrableOn_exp_mul_density (q := q) hT100).add
          (integrableOn_gauss_mul_density (q := q) hδ hT100)
      refine hsplit.congr_fun (fun s hs => ?_) measurableSet_Ioi
      have hs0 : (0:ℝ) < s := lt_of_lt_of_le hT0 hs.le
      have hbE : branchEnv δ s = exp (-0.1598 * s) +
          exp (-0.1065 * (s / (π * |δ|)) ^ 2) := by
        simp [branchEnv, hδ, abs_of_pos hs0]
      show exp (-0.1598 * s) * TailIntegral123.countDensity q s +
          exp (-0.1065 * (s / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q s =
        branchEnv δ s * TailIntegral123.countDensity q s
      rw [hbE]
      ring
  have hstep3 : ∫ s in Set.Ioi T, hfun s * V s =
      ∫ s in Set.Ioi T, branchEnv δ s * TailIntegral123.countDensity q s := by
    have hderiv_u : ∀ s ∈ Set.Ioi T, HasDerivAt (branchEnv δ) (-(hfun s)) s := by
      intro s hs
      have hs0 : (0:ℝ) < s := lt_of_lt_of_le hT0 hs.le
      have h := hasDerivAt_branchEnv (δ := δ) hs0
      simpa [hhfun] using h
    have hderiv_v : ∀ s ∈ Set.Ioi T, HasDerivAt V (TailIntegral123.countDensity q s) s := by
      intro s hs
      have hs0 : (0:ℝ) < s := lt_of_lt_of_le hT0 hs.le
      have h := hasDerivAt_bookTail (q := q) (T := T) hs0
      simpa [hV] using h
    have hint_u'v : MeasureTheory.IntegrableOn (fun s => -(hfun s) * V s) (Set.Ioi T)
        MeasureTheory.volume := by
      have h := hint_hV.neg
      refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
      simp only [Pi.neg_apply]
      ring
    have hcontV : ContinuousAt V T := by
      have h := hasDerivAt_bookTail (q := q) (T := T) hT0
      have h' : HasDerivAt V (TailIntegral123.countDensity q T) T := by
        simpa [hV] using h
      exact h'.continuousAt
    have hboundary0 : Filter.Tendsto (fun s => branchEnv δ s * V s)
        (nhdsWithin T (Set.Ioi T)) (nhds (branchEnv δ T * V T)) :=
      ((continuous_branchEnv δ).continuousAt.mul hcontV).continuousWithinAt
    have hboundaryinf : Filter.Tendsto (fun s => branchEnv δ s * V s) Filter.atTop (nhds 0) := by
      have := tendsto_branchEnv_mul_bookTail (q := q) (δ := δ) hT100
      simpa [hV] using this
    have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := T)
      (a' := branchEnv δ T * V T) (b' := 0)
      (u := fun s => branchEnv δ s) (v := V) (u' := fun s => -(hfun s))
      (v' := fun s => TailIntegral123.countDensity q s)
      hderiv_u hderiv_v hint_uv' hint_u'v hboundary0 hboundaryinf
    have hVT : V T = 0 := by
      simp only [hV]
      ring
    have hneg : ∫ s in Set.Ioi T, -(hfun s) * V s = -(∫ s in Set.Ioi T, hfun s * V s) := by
      have heq : (fun s => -(hfun s) * V s) = fun s => -(hfun s * V s) := funext (fun s => by ring)
      rw [heq, MeasureTheory.integral_neg]
    rw [hneg, hVT, mul_zero] at hIBP
    linarith [hIBP]
  have hstep4 : ∫ s in Set.Ioi T, branchEnv δ s * TailIntegral123.countDensity q s =
      TailIntegral123.expTailIntegral q T + TailIntegral123.gaussianTailIntegral q δ T := by
    by_cases hδ : δ = 0
    · have hcongr : Set.EqOn (fun s => branchEnv δ s * TailIntegral123.countDensity q s)
          (fun s => exp (-0.1598 * s) * TailIntegral123.countDensity q s) (Set.Ioi T) := by
        intro s hs
        have hs0 : (0:ℝ) < s := lt_of_lt_of_le hT0 hs.le
        have hbE : branchEnv δ s = exp (-0.1598 * s) := by
          simp [branchEnv, hδ, abs_of_pos hs0]
        show branchEnv δ s * TailIntegral123.countDensity q s =
          exp (-0.1598 * s) * TailIntegral123.countDensity q s
        rw [hbE]
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
      have hg : TailIntegral123.gaussianTailIntegral q δ T = 0 := by
        simp [TailIntegral123.gaussianTailIntegral, hδ]
      rw [hg, add_zero]
      rfl
    · have h1 := integrableOn_exp_mul_density (q := q) hT100
      have h2 := integrableOn_gauss_mul_density (q := q) hδ hT100
      have hcongr : Set.EqOn (fun s => branchEnv δ s * TailIntegral123.countDensity q s)
          (fun s => exp (-0.1598 * s) * TailIntegral123.countDensity q s +
            exp (-0.1065 * (s / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q s)
          (Set.Ioi T) := by
        intro s hs
        have hs0 : (0:ℝ) < s := lt_of_lt_of_le hT0 hs.le
        have hbE : branchEnv δ s = exp (-0.1598 * s) +
            exp (-0.1065 * (s / (π * |δ|)) ^ 2) := by
          simp [branchEnv, hδ, abs_of_pos hs0]
        show branchEnv δ s * TailIntegral123.countDensity q s =
          exp (-0.1598 * s) * TailIntegral123.countDensity q s +
            exp (-0.1065 * (s / (π * |δ|)) ^ 2) * TailIntegral123.countDensity q s
        rw [hbE]
        ring
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
        MeasureTheory.integral_add h1 h2]
      have hg : TailIntegral123.gaussianTailIntegral q δ T =
          ∫ t in Set.Ioi T, exp (-0.1065 * (t / (π * |δ|)) ^ 2) *
            TailIntegral123.countDensity q t := by
        simp [TailIntegral123.gaussianTailIntegral, hδ]
      rw [hg]
      rfl
  have hstep5 : ∫ s in Set.Ioi T, hfun s = branchEnv δ T := by
    have h := branchEnv_eq_integral (δ := δ) hT0
    simpa [hhfun] using h.symm
  rw [habel]
  have hfin : ∫ s in Set.Ioi T, hfun s * Nind s ≤
      2 * (TailIntegral123.expTailIntegral q T + TailIntegral123.gaussianTailIntegral q δ T) +
        4 * branchEnv δ T * ZeroCount1623.bookError q T := by
    refine hstep1.trans (le_of_eq ?_)
    rw [hstep2, hstep3, hstep4, hstep5]
    simp only [hc]
    ring
  exact hfin

/-- PROVED, CONDITIONAL ON hB, the book zero count of display 4.26 on page 38, on hcor, the
k equal to 0 case of Corollary 3.2 on page 10, and on hcount, the counting bound of
`two_sided_envelope_count_le` for this character. P0014 Lemma 4.5, page 41, restated
without the pairing of display 4.33: the multiplicity weighted Mellin mass of the zeros above
height T on both sides is summable and at most 8.452 times the two tail integrals plus
16.904 times the envelope at T times bookError at T. Summability comes from the unit shell
count of `MainTail123.tail_shell_count_le_quadratic_of_book`, and the per zero comparison from
`SplitGaussian123.tail_mass_le_two_sided_envelope`. -/
theorem tail_mass_bound_unpaired_of_count (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im)
    (hcount : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) ≤
      2 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      4 * branchEnv δ T * ZeroCount1623.bookError q T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      8.452 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      16.904 * branchEnv δ T * ZeroCount1623.bookError q T := by
  have hT1 : 1 ≤ T := by have := (le_max_right _ _).trans hT; linarith
  have hs := tail_envelope_summable_of_shell_count χ δ T (2 * (q : ℝ) + 18) hT1
    (MainTail123.tail_shell_count_le_quadratic_of_book hB χ hχ T)
  obtain ⟨hm, hle⟩ := tail_mass_le_two_sided_envelope χ δ T hT hcor hs
  refine ⟨hm, hle.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hcount (by norm_num : (0 : ℝ) ≤ 4.226)
  linarith

/-- The restated LEAF of design queue Q1, replacing the bound half of
`SplitGaussian123.tail_mass_of_corollary`. P0014 Lemma 4.5, page 41, displays 4.33 to 4.35,
for every primitive chi, with no pairing and with the boundary term of the Stieltjes
summation. CONDITIONAL ON hB, the book zero count of display 4.26 on page 38, and on hcor,
Corollary 3.2 at k equal to 0 on page 10. Assembled from the PROVED reduction
`tail_mass_bound_unpaired_of_count` and the open counting LEAF
`two_sided_envelope_count_le`, so it depends on that one sorry. -/
theorem tail_mass_bound_unpaired (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      8.452 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      16.904 * branchEnv δ T * ZeroCount1623.bookError q T :=
  tail_mass_bound_unpaired_of_count hB q χ hχ δ T hT hcor
    (two_sided_envelope_count_le hB q χ hχ δ T hT)

end LeanLab.HelfgottMajor.DQTailUnpaired

#print axioms LeanLab.HelfgottMajor.DQTailUnpaired.branchEnv_nonneg
#print axioms LeanLab.HelfgottMajor.DQTailUnpaired.two_sided_envelope_count_le
#print axioms LeanLab.HelfgottMajor.DQTailUnpaired.tail_mass_bound_unpaired_of_count
#print axioms LeanLab.HelfgottMajor.DQTailUnpaired.tail_mass_bound_unpaired
