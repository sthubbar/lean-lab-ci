/-
AI wrote this Lean code. Codex task394, 2026-11-05.
Supporting steps and a supply decomposition of page 337, display 1.4.
The integral comparison in gammaSeq_norm_le adapts Mathlib Gamma.Beta.
Copyright 2023 David Loeffler. Released under Apache 2.0 as in Mathlib LICENSE.
Binary Goldbach is open.
-/
import Mathlib
open Complex Filter Topology Set MeasureTheory intervalIntegral Metric
namespace LeanLab.Zinoviev1997.Decomp394b
/-- Supporting finite Euler product differentiation for display 1.4 on p. 337. -/
theorem gammaSeq_logDeriv {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun z : ℂ => Complex.GammaSeq z n) s =
      Complex.log (n : ℂ) - ∑ j ∈ Finset.range (n+1), 1 / (s+j) := by
  have hshift (j : ℕ) : s+(j : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hpow := (hasDerivAt_id s).const_cpow (c := (n : ℂ))
    (Or.inl (by exact_mod_cast hn))
  simp only [id_eq, mul_one] at hpow
  have hpnez : (n : ℂ)^s ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hn]
  have hf : (n : ℂ)^s * n.factorial ≠ 0 :=
    mul_ne_zero hpnez (by exact_mod_cast Nat.factorial_ne_zero n)
  have hg : (∏ j ∈ Finset.range (n+1), (s+(j : ℂ))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hshift j
  have hdf : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ)^z * n.factorial) s :=
    hpow.differentiableAt.mul_const _
  have hdg : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ Finset.range (n+1), (z+(j : ℂ))) s := by
    fun_prop
  have hprod : logDeriv (fun z : ℂ => ∏ j ∈ Finset.range (n+1), (z+(j : ℂ))) s =
      ∑ j ∈ Finset.range (n+1), 1/(s+(j : ℂ)) := by
    rw [logDeriv_fun_prod (fun j hj => hshift j) (fun j hj => by fun_prop)]
    apply Finset.sum_congr rfl
    intro j hj
    simp [logDeriv_apply]
  change logDeriv (fun z : ℂ => ((n : ℂ)^z * n.factorial) /
    (∏ j ∈ Finset.range (n+1), (z+(j : ℂ)))) s = _
  rw [logDeriv_fun_div s hf hg hdf hdg, hprod,
    logDeriv_mul_const s (n.factorial : ℂ) (by exact_mod_cast Nat.factorial_ne_zero n)]
  congr 1
  rw [logDeriv_apply, hpow.deriv]
  field_simp

/-- Supporting finite reciprocal rearrangement for display 1.4 on p. 337. -/
theorem gamma_reciprocal_rearrangement (w : ℂ) (n : ℕ) :
    (1/2 : ℂ) * (∑ j ∈ Finset.range (n+1), 1/(w/2+j)) =
      1/w + (1/2 : ℂ) * (harmonic n : ℂ) -
      ∑ k ∈ Finset.range n,
        (1/(2*((k+1 : ℕ) : ℂ)) - 1/(w+2*(k+1 : ℕ))) := by
  have hscale (u : ℂ) : (1/2 : ℂ) * (1/(u/2)) = 1/u := by
    simp only [one_div, inv_div]
    ring
  induction n with
  | zero => simpa using hscale w
  | succ n ih =>
    rw [Finset.sum_range_succ (n := n+1), harmonic_succ]
    conv_rhs => rw [Finset.sum_range_succ]
    push_cast at ih ⊢
    have he : w/2 + ((n : ℂ)+1) = (w+2*((n : ℂ)+1))/2 := by ring
    rw [mul_add, ih, he]
    rw [hscale]
    simp only [one_div, mul_inv_rev]
    ring

/-- Supporting finite Euler approximation formula for display 1.4 on p. 337. -/
theorem gammaSeq_normalized_logDeriv {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : n ≠ 0) :
    (1/2 : ℂ) * logDeriv (fun z : ℂ => Complex.GammaSeq z n) (w/2) =
      (1/2 : ℂ) * (Complex.log (n : ℂ) - (harmonic n : ℂ)) - 1/w +
      ∑ k ∈ Finset.range n,
        (1/(2*((k+1 : ℕ) : ℂ)) - 1/(w+2*(k+1 : ℕ))) := by
  rw [gammaSeq_logDeriv (by simpa using (show 0 < w.re/2 by linarith)) hn]
  have hr := gamma_reciprocal_rearrangement w n
  linear_combination -hr

/-- Supporting real finite Euler formula for display 1.4 on p. 337. -/
theorem gammaSeq_real_normalized {σ T : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : n ≠ 0) :
    (1/2 : ℝ) * (logDeriv (fun z : ℂ => Complex.GammaSeq z n)
      (((σ : ℂ)+T*I)/2)).re =
      (1/2 : ℝ) * (Real.log n - (harmonic n : ℝ)) -
      (1/((σ : ℂ)+T*I)).re +
      ∑ k ∈ Finset.range n,
        (1/(2*((k+1 : ℕ) : ℂ)) - 1/((σ : ℂ)+T*I+2*(k+1 : ℕ))).re := by
  have hc := gammaSeq_normalized_logDeriv
    (w := (σ : ℂ)+T*I) (by simpa using hσ) hn
  have hr := congrArg Complex.re hc
  have he : (∑ k ∈ Finset.range n,
      (1/(2*((k+1 : ℕ) : ℂ)) - 1/((σ : ℂ)+T*I+2*(k+1 : ℕ)))).re =
      ∑ k ∈ Finset.range n,
      (1/(2*((k+1 : ℕ) : ℂ)) - 1/((σ : ℂ)+T*I+2*(k+1 : ℕ))).re := by
    exact map_sum Complex.reAddGroupHom _ _
  rw [Complex.add_re, he] at hr
  simpa [Complex.log_re] using hr

/-- Supporting limit of the finite Euler derivatives for display 1.4 on p. 337.
Summability is an explicit input. No derivative limit for Gamma is assumed here. -/
theorem gammaSeq_real_logDeriv_limit {σ T : ℝ} (hσ : 0 < σ)
    (hs : Summable (fun k : ℕ =>
      (1/(2*((k+1 : ℕ) : ℂ)) - 1/((σ : ℂ)+T*I+2*(k+1 : ℕ))).re)) :
    Tendsto (fun n : ℕ => (1/2 : ℝ) *
      (logDeriv (fun z : ℂ => Complex.GammaSeq z n) (((σ : ℂ)+T*I)/2)).re)
      atTop (nhds (-Real.eulerMascheroniConstant/2 - (1/((σ : ℂ)+T*I)).re +
        ∑' k : ℕ,
          (1/(2*((k+1 : ℕ) : ℂ)) - 1/((σ : ℂ)+T*I+2*(k+1 : ℕ))).re)) := by
  have hh : Tendsto (fun n : ℕ => (1/2 : ℝ) * (Real.log n - (harmonic n : ℝ)))
      atTop (nhds (-Real.eulerMascheroniConstant/2)) := by
    convert (Real.tendsto_harmonic_sub_log.neg).const_mul (1/2 : ℝ) using 1
    · funext n
      ring
    · ring
  have ht := (hh.sub_const (1/((σ : ℂ)+T*I)).re).add hs.hasSum.tendsto_sum_nat
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (gammaSeq_real_normalized hσ hn).symm

/-- Supporting differentiability of the finite Euler approximations for display 1.4 on p. 337. -/
theorem gammaSeq_differentiableAt {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.GammaSeq z n) s := by
  have hshift (j : ℕ) : s+(j : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ)^z) s :=
    differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hn))
  have hprod : DifferentiableAt ℂ (fun z : ℂ =>
      ∏ j ∈ Finset.range (n+1), (z+(j : ℂ))) s := by fun_prop
  have hne : (∏ j ∈ Finset.range (n+1), (s+(j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => hshift j
  exact (hpow.mul_const (n.factorial : ℂ)).div hprod hne

/-- Supporting bound for the uniform Euler limit needed in display 1.4 on p. 337. -/
theorem gammaSeq_norm_le {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.GammaSeq s n‖ ≤ Real.Gamma s.re := by
  let f : ℝ → ℂ := Set.indicator (Ioc 0 (n : ℝ)) fun x : ℝ =>
    ((1-x/n)^n : ℝ) * (x : ℂ)^(s-1)
  let g : ℝ → ℝ := fun x => Real.exp (-x) * x^(s.re-1)
  have hf : Integrable f (volume.restrict (Ioi 0)) := by
    dsimp only [f]
    rw [integrable_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (_ : ℝ) _)),
      IntegrableOn, Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self,
      ← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by positivity : (0 : ℝ) ≤ n)]
    apply IntervalIntegrable.continuousOn_mul
    · refine intervalIntegral.intervalIntegrable_cpow' ?_
      rwa [Complex.sub_re, Complex.one_re, ← zero_sub, sub_lt_sub_iff_right]
    · fun_prop
  have hg : Integrable g (volume.restrict (Ioi 0)) := Real.GammaIntegral_convergent hs
  have hb : ∀ x ∈ Ioi (0 : ℝ), ‖f x‖ ≤ g x := by
    intro x hx
    dsimp only [f, g]
    rcases lt_or_ge (n : ℝ) x with hxn | hxn
    · rw [indicator_of_notMem (notMem_Ioc_of_gt hxn), norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)
    · rw [indicator_of_mem (mem_Ioc.mpr ⟨hx,hxn⟩), norm_mul,
        Complex.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr
          (div_le_one_of_le₀ hxn (by positivity))) _),
        Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_right (Real.one_sub_div_pow_le_exp_neg hxn)
        (Real.rpow_nonneg hx.le _)
  have he : Complex.GammaSeq s n = ∫ x in Ioi (0 : ℝ), f x := by
    rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn]
    dsimp only [f]
    rw [MeasureTheory.integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ n)]
  rw [he]
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), ‖f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (0 : ℝ), g x := by
      apply integral_mono_ae hf.norm hg
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hb)
    _ = Real.Gamma s.re := (Real.Gamma_eq_integral hs).symm

/-- Supporting equicontinuity of the Euler approximations for display 1.4 on p. 337. -/
theorem gammaSeq_equicontinuousAt {s : ℂ} (hs : 0 < s.re) :
    EquicontinuousAt (fun n : ℕ => fun z : ℂ => Complex.GammaSeq z n) s := by
  have hzero (z : ℂ) : Complex.GammaSeq z 0 = 0 := by
    by_cases hz : z = 0 <;> simp [Complex.GammaSeq, hz, Complex.zero_cpow]
  have hdiff (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
      DifferentiableAt ℂ (fun w : ℂ => Complex.GammaSeq w n) z := by
    by_cases hn : n = 0
    · subst n
      have he : (fun w : ℂ => Complex.GammaSeq w 0) = fun _ => 0 := funext hzero
      rw [he]
      fun_prop
    · exact gammaSeq_differentiableAt hz hn
  let M := Real.Gamma s.re + 1
  have hM : 0 < M := by
    dsimp [M]
    linarith [Real.Gamma_pos_of_pos hs]
  have hgc : ContinuousAt (fun z : ℂ => Real.Gamma z.re) s :=
    (Real.differentiableOn_Gamma_Ioi.differentiableAt
      (isOpen_Ioi.mem_nhds hs)).continuousAt.comp Complex.continuous_re.continuousAt
  have hbounded : ∀ᶠ z : ℂ in nhds s, 0 < z.re ∧ Real.Gamma z.re < M := by
    have hg := hgc.tendsto.eventually
      (eventually_lt_nhds (show Real.Gamma s.re < M by dsimp [M]; linarith))
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs, hg] with z hz hgz
    exact ⟨hz, hgz⟩
  obtain ⟨R, hR, hRB⟩ := Metric.mem_nhds_iff.mp hbounded
  let r := R/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hlocal {z : ℂ} (hz : z ∈ closedBall s (3*r)) :
      0 < z.re ∧ Real.Gamma z.re ≤ M := by
    have hzR : z ∈ ball s R := by
      rw [mem_ball]
      exact lt_of_le_of_lt (mem_closedBall.mp hz) (by dsimp [r]; linarith)
    have hh := hRB hzR
    exact ⟨hh.1, hh.2.le⟩
  have hnorm (n : ℕ) {z : ℂ} (hz : z ∈ closedBall s (3*r)) :
      ‖Complex.GammaSeq z n‖ ≤ M := by
    by_cases hn : n = 0
    · subst n
      rw [hzero, norm_zero]
      exact hM.le
    · exact (gammaSeq_norm_le (hlocal hz).1 hn).trans (hlocal hz).2
  have hder (n : ℕ) {z : ℂ} (hz : z ∈ closedBall s r) :
      ‖deriv (fun w : ℂ => Complex.GammaSeq w n) z‖ ≤ M/r := by
    have hbig {w : ℂ} (hw : w ∈ closedBall z r) : w ∈ closedBall s (3*r) := by
      calc
        dist w s ≤ dist w z + dist z s := dist_triangle _ _ _
        _ ≤ r+r := add_le_add hw hz
        _ ≤ 3*r := by linarith
    have hsub : closedBall z r ⊆ {w : ℂ | 0 < w.re} := fun w hw => (hlocal (hbig hw)).1
    rw [← Complex.cderiv_eq_deriv (Complex.isOpen_re_gt 0)
      (fun w hw => (hdiff n w hw).differentiableWithinAt) hr hsub]
    apply Complex.norm_cderiv_le hr
    intro w hw
    exact hnorm n (hbig (mem_closedBall.mpr (mem_sphere.mp hw).le))
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  have hC : 0 ≤ M/r := by positivity
  have hCp : 0 < M/r+1 := by positivity
  refine ⟨min r (ε/(M/r+1)), lt_min hr (div_pos hε hCp), ?_⟩
  intro y hy n
  have hyr : y ∈ closedBall s r := (lt_of_lt_of_le hy (min_le_left _ _)).le
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun w : ℂ => Complex.GammaSeq w n)
    (fun z hz => hdiff n z (hlocal ((closedBall_subset_closedBall (by linarith)) hz)).1)
    (fun z hz => hder n hz) (convex_closedBall s r)
    (mem_closedBall_self hr.le) hyr
  have hsmall := lt_of_lt_of_le hy (min_le_right r (ε/(M/r+1)))
  rw [lt_div_iff₀ hCp] at hsmall
  have hp : M/r * dist y s < ε := by nlinarith [dist_nonneg (x := y) (y := s)]
  rw [dist_eq_norm, norm_sub_rev]
  exact hh.trans_lt (by simpa only [dist_eq_norm] using hp)

/-- LEAF. Page 337, display 1.4, a supporting uniform Euler limit for the Gamma factor.
The pointwise Euler limit is upgraded by local Gamma bounds, Cauchy estimates,
equicontinuity and compactness. This supplies the Gamma derivative limit without a cited input. -/
theorem gammaSeq_locally_uniform :
    TendstoLocallyUniformlyOn (fun n : ℕ => fun s : ℂ => Complex.GammaSeq s n)
      Complex.Gamma atTop {s : ℂ | 0 < s.re} := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact (Complex.isOpen_re_gt 0)).mpr
  intro K hKS hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he : Equicontinuous (fun n : ℕ => fun z : K => Complex.GammaSeq z n) := by
    apply (equicontinuous_restrict_iff (fun n : ℕ => fun z : ℂ => Complex.GammaSeq z n)).mpr
    intro z hz
    exact (gammaSeq_equicontinuousAt (hKS hz)).equicontinuousWithinAt K
  have hp : Tendsto (fun n : ℕ => fun z : K => Complex.GammaSeq z n) atTop
      (nhds (fun z : K => Complex.Gamma z)) :=
    tendsto_pi_nhds.mpr fun z => Complex.GammaSeq_tendsto_Gamma z
  have hu := (he.tendsto_uniformFun_iff_pi atTop (fun z : K => Complex.Gamma z)).mpr hp
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  exact UniformFun.tendsto_iff_tendstoUniformly.mp hu

/-- The derivative limit for display 1.4 on p. 337.
The local uniform Euler limit is proved. No cited input remains. -/
theorem gammaSeq_logDeriv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => logDeriv (fun z : ℂ => Complex.GammaSeq z n) s)
      atTop (nhds (Complex.digamma s)) := by
  apply Complex.logDeriv_tendsto (Complex.isOpen_re_gt 0) hs gammaSeq_locally_uniform
  · filter_upwards [eventually_ne_atTop 0] with n hn
    intro z hz
    exact (gammaSeq_differentiableAt hz hn).differentiableWithinAt
  · exact Complex.Gamma_ne_zero_of_re_pos hs

/-- The gamma reciprocal identity needed in display 1.4 on p. 337.
The local uniform Euler limit is proved. No cited input remains. Its finite formula and sum limit are proved. -/
theorem digamma_real_series_of_summable {σ T : ℝ} (hσ : 0 < σ)
    (hs : Summable (fun k : ℕ =>
      (1/(2*((k+1 : ℕ) : ℂ)) - 1/((σ : ℂ)+T*I+2*(k+1 : ℕ))).re)) :
    (1/2 : ℝ) * (Complex.digamma (((σ : ℂ)+T*I)/2)).re =
      -Real.eulerMascheroniConstant/2 - (1/((σ : ℂ)+T*I)).re +
        ∑' k : ℕ,
          (1/(2*((k+1 : ℕ) : ℂ)) - 1/((σ : ℂ)+T*I+2*(k+1 : ℕ))).re := by
  have ha := ((Complex.continuous_re.tendsto _).comp
    (gammaSeq_logDeriv_tendsto (s := ((σ : ℂ)+T*I)/2)
      (by simpa using (show 0 < σ/2 by linarith)))).const_mul (1/2 : ℝ)
  exact tendsto_nhds_unique ha (gammaSeq_real_logDeriv_limit hσ hs)

end LeanLab.Zinoviev1997.Decomp394b
