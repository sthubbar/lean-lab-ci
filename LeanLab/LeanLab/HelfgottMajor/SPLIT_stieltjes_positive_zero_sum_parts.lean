import LeanLab.HelfgottMajor.Decomp431a

/-!
Split of the LEAF `stieltjes_positive_zero_sum` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral_stieltjes`, following the proof of
book Lemma 16.9, displays 16.20 and 16.21 on book pages 431 and 432 of P0014 Part IV, as applied
in the proof of Lemma 16.10 on book page 433 with `y = 1` and `f t = |G_δ (1/2 + i t)|`.

Notation in the doc comments: `G t` is the norm of `gaussianMellin δ` at `1/2 + i t`, `N t` the
multiplicity weighted count of zeros with `0 < re < 1` and `0 < im ≤ t`, and
`M t = t / (2 π) * log (q t / (2 π e))`.  The leaves are the Stieltjes integration by parts
against `dN`, the fundamental theorem of calculus for `G`, the integration by parts against `dM`,
and the integrability facts that let the integral of `G' * (N + c - M)` be split linearly.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

open MeasureTheory Filter Set Asymptotics
open scoped Topology

/-- The Gaussian Mellin transform `G_δ` is holomorphic on the right half plane, the strip of
definition used on page 32 of P0014 and in the proof of book Lemma 16.10, page 433. -/
private lemma sp_gm_differentiableAt (δ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (gaussianMellin δ) s := by
  let f : ℝ → ℂ := fun t => (Real.exp (-t ^ 2 / 2) : ℂ) * e (δ * t)
  have hn (t : ℝ) : ‖f t‖ = Real.exp (-t ^ 2 / 2) := by
    have he : ‖e (δ * t)‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
    dsimp only [f]
    rw [norm_mul, he, mul_one, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hc : Continuous f := by unfold f e; fun_prop
  have htop : f =O[atTop] (fun t : ℝ => Real.exp (-1 * t)) := by
    rw [← isBigO_norm_left]
    simp_rw [hn]
    simpa only [one_mul, mul_one, neg_mul, mul_neg, div_eq_mul_inv, mul_comm] using
      (exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2)).isBigO
  have hbot : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply isBigO_iff.mpr
    refine ⟨1, Eventually.of_forall fun t => ?_⟩
    simp only [hn, neg_zero, rpow_zero, norm_one, mul_one]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  exact mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0 : ℝ) < 1)
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi) htop hbot hs

/-- `u ↦ G_δ (1/2 + i u)` is `C^1` on the real line. -/
private lemma sp_contDiff (δ : ℝ) :
    ContDiff ℝ 1 (fun u : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ (gaussianMellin δ) {s : ℂ | 0 < s.re} :=
    fun s hs => (sp_gm_differentiableAt δ hs).differentiableWithinAt
  have hG : ContDiffOn ℂ 1 (gaussianMellin δ) {s : ℂ | 0 < s.re} := hD.contDiffOn hU
  have hGR : ContDiffOn ℝ 1 (gaussianMellin δ) {s : ℂ | 0 < s.re} := hG.restrict_scalars ℝ
  have hh : ContDiff ℝ 1 (fun u : ℝ => (1 / 2 : ℂ) + (u : ℝ) * Complex.I) := by
    have h0 : ContDiff ℝ 1 (fun u : ℝ => Complex.ofRealCLM u) := Complex.ofRealCLM.contDiff
    exact contDiff_const.add (h0.mul contDiff_const)
  rw [← contDiffOn_univ]
  exact hGR.comp hh.contDiffOn (fun u _ => by simp)

/-- `f t = |G_δ (1/2 + i t)|` is absolutely continuous on every interval, as the norm of a
`C^1` function, which is what the integrations by parts in Lemma 16.9, page 431, use. -/
private lemma sp_ac (δ a b : ℝ) : AbsolutelyContinuousOnInterval
    (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) a b :=
  LipschitzWith.comp_absolutelyContinuousOnInterval (f := fun z : ℂ => ‖z‖) lipschitzWith_one_norm
    ((sp_contDiff δ).contDiffOn.absolutelyContinuousOnInterval)

/-- The main term `M t = t / (2 π) * log (q t / (2 π e))` has derivative
`(1 / 2 π) log (q t / 2 π)`, book Lemma 16.9, page 431. -/
private lemma sp_M_hasDerivAt (q : ℕ) [NeZero q] {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => u / (2 * π) * log ((q : ℝ) * u / (2 * π * exp 1)))
      (1 / (2 * π) * log ((q : ℝ) * t / (2 * π))) t := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hpos : 0 < (q : ℝ) * t / (2 * π * exp 1) := by positivity
  have h1 : HasDerivAt (fun u : ℝ => u / (2 * π)) (1 / (2 * π)) t :=
    (hasDerivAt_id t).div_const _
  have h2 : HasDerivAt (fun u : ℝ => (q : ℝ) * u / (2 * π * exp 1))
      ((q : ℝ) * 1 / (2 * π * exp 1)) t :=
    ((hasDerivAt_id t).const_mul _).div_const _
  have h3 := h2.log hpos.ne'
  have hl : log ((q : ℝ) * t / (2 * π * exp 1)) = log ((q : ℝ) * t / (2 * π)) - 1 := by
    rw [show (q : ℝ) * t / (2 * π * exp 1) = ((q : ℝ) * t / (2 * π)) / exp 1 by
      field_simp, log_div (by positivity) (exp_pos 1).ne', log_exp]
  convert h1.mul h3 using 1
  rw [hl]
  field_simp
  ring

private lemma sp_M_contDiffOn (q : ℕ) [NeZero q] {T : ℝ} (hT : 1 ≤ T) :
    ContDiffOn ℝ 1 (fun u : ℝ => u / (2 * π) * log ((q : ℝ) * u / (2 * π * exp 1)))
      (uIcc 1 T) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply ContDiffOn.mul (contDiffOn_id.div_const _)
  apply ContDiffOn.log ((contDiffOn_const.mul contDiffOn_id).div_const _)
  intro x hx
  rw [uIcc_of_le hT] at hx
  have : (0 : ℝ) < x := by linarith [hx.1]
  simp only [id]
  positivity

/-- The zeros of `L(s, χ)` in the strip `0 < re s < 1` with `|im s| ≤ T` are finitely many: the
function is entire for `χ ≠ 1`, has only the pole at 1 for the trivial character, and is not
identically zero.  Same argument as `LZeros_finite` in `LeanLab.DERZ1997.Decomp1529a`. -/
private lemma sp_zeros_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {z : ℂ | DirichletCharacter.LFunction χ z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T}.Finite := by
  have hb : ∀ z ∈ {z : ℂ | DirichletCharacter.LFunction χ z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧
      |z.im| ≤ T}, ‖z‖ ≤ |T| + 2 := by
    intro z hz
    have ht : |z.im| ≤ |T| := hz.2.2.2.trans (le_abs_self T)
    have hr : |z.re| ≤ 1 := by rw [abs_of_pos hz.2.1]; exact hz.2.2.1.le
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have finite_zeros : ∀ (f : ℂ → ℂ), Differentiable ℂ f →
      (∃ z, f z ≠ 0) → {z : ℂ | ‖z‖ ≤ |T| + 2 ∧ f z = 0}.Finite := by
    intro f hf ⟨w, hw⟩
    have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
    have hd : f ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ := by
      simpa [Filter.codiscrete] using ha.preimage_zero_mem_codiscreteWithin hw (Set.mem_univ w)
        isConnected_univ
    have hclosed : IsClosed (f ⁻¹' {0}) := isClosed_singleton.preimage hf.continuous
    have hdiscrete : IsDiscrete (f ⁻¹' {0}) := by
      simpa using (mem_codiscrete'.mp hd).2
    have hcompact := (isCompact_closedBall (0 : ℂ) (|T| + 2)).inter_right hclosed
    have hfinite := hcompact.finite (hdiscrete.mono Set.inter_subset_right)
    convert hfinite using 1
    ext z
    simp [Metric.mem_closedBall, dist_zero_right]
  by_cases hχ : χ = 1
  · subst χ
    have hf := finite_zeros (DirichletCharacter.LFunctionTrivChar₁ q)
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
      ⟨1, DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q⟩
    apply hf.subset
    intro z hz
    refine ⟨hb z hz, ?_⟩
    have hz1 : z ≠ 1 := by intro h; simpa [h] using hz.2.2.1
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1]
    exact mul_eq_zero_of_right _ hz.1
  · have hf := finite_zeros (DirichletCharacter.LFunction χ)
      (DirichletCharacter.differentiable_LFunction hχ)
      ⟨2, DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)⟩
    apply hf.subset
    intro z hz
    exact ⟨hb z hz, hz.1⟩

/-- For `t ≤ T` the counting function `N t` is the finite sum over the zeros of height at most
`T` of the multiplicities of those with `0 < im ≤ t`. -/
private lemma sp_N_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) {t : ℝ}
    (ht : t ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) =
      ∑ ρ ∈ (sp_zeros_finite χ T).toFinset,
        if 0 < ρ.im ∧ ρ.im ≤ t then
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) else 0 := by
  classical
  rw [show (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) =
      ∑' ρ : ℂ, Set.indicator {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ρ from
      tsum_subtype {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))]
  rw [tsum_eq_sum (s := (sp_zeros_finite χ T).toFinset)]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hρ
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hρ.1, hρ.2.1, hρ.2.2.1, true_and]
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hρ
    rw [Set.indicator_of_notMem]
    intro h
    exact hρ ⟨h.1, h.2.1, h.2.2.1, abs_le.2 ⟨by linarith [h.2.2.2.1, h.2.2.2.2, ht], h.2.2.2.2.trans ht⟩⟩

private lemma sp_ite_mono (γ m t s : ℝ) (hm : 0 ≤ m) (hst : s ≤ t) :
    (if 0 < γ ∧ γ ≤ s then m else 0) ≤ (if 0 < γ ∧ γ ≤ t then m else 0) := by
  by_cases h1 : 0 < γ ∧ γ ≤ s
  · rw [if_pos h1, if_pos ⟨h1.1, h1.2.trans hst⟩]
  · rw [if_neg h1]
    split_ifs
    · exact hm
    · exact le_rfl

private lemma sp_N_mono {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    MonotoneOn (fun t : ℝ => ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) (Icc 1 T) := by
  intro s hs t ht hst
  simp only
  rw [sp_N_eq χ T hs.2, sp_N_eq χ T ht.2]
  exact Finset.sum_le_sum fun ρ _ => sp_ite_mono _ _ _ _ (Nat.cast_nonneg _) hst

/-- `f' g` is integrable on `[1, T]` for `f t = |G_δ (1/2 + i t)|` and `g` monotone and
nonnegative there, the regularity used in the proof of Lemma 16.9, page 431. -/
private lemma sp_int_mul_mono (δ T : ℝ) (hT : 1 ≤ T) {g : ℝ → ℝ}
    (hg : MonotoneOn g (Icc 1 T)) (hg0 : ∀ t ∈ Icc 1 T, 0 ≤ g t) :
    IntervalIntegrable (fun t =>
      deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t * g t)
      volume 1 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hD := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
    (sp_ac δ 1 T).intervalIntegrable_deriv
  refine Integrable.mul_bdd (c := g T) hD
    ((aemeasurable_restrict_of_monotoneOn measurableSet_Ioc
      (hg.mono Ioc_subset_Icc_self)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
  have hx' : x ∈ Icc 1 T := Ioc_subset_Icc_self hx
  rw [Real.norm_of_nonneg (hg0 x hx')]
  exact hg hx' ⟨hT, le_rfl⟩ hx.2

/-- The contribution of one zero of height `γ ≤ T` to the integration by parts. -/
private lemma sp_term (δ T γ m : ℝ) (hT : 1 ≤ T) (hγ : γ ≤ T) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
        (if 0 < γ ∧ γ ≤ T then m else 0) -
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ *
        (if 0 < γ ∧ γ ≤ (1 : ℝ) then m else 0) -
      (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (if 0 < γ ∧ γ ≤ t then m else 0)) =
      if 1 < γ then m * ‖gaussianMellin δ ((1 / 2 : ℂ) + (γ : ℝ) * Complex.I)‖ else 0 := by
  by_cases h0 : 0 < γ
  · by_cases h1 : γ ≤ 1
    · have hI : (∫ t in (1 : ℝ)..T,
          deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
            (if 0 < γ ∧ γ ≤ t then m else 0)) =
          ∫ t in (1 : ℝ)..T,
            deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t * m := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT] at ht
        simp only
        rw [if_pos ⟨h0, h1.trans ht.1⟩]
      rw [hI, intervalIntegral.integral_mul_const, (sp_ac δ 1 T).integral_deriv_eq_sub,
        if_pos ⟨h0, hγ⟩, if_pos ⟨h0, h1⟩, if_neg (not_lt.2 h1)]
      ring
    · push_neg at h1
      have hi1 : IntervalIntegrable (fun t =>
          deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
            (if 0 < γ ∧ γ ≤ t then m else 0)) volume 1 γ := by
        refine (intervalIntegrable_congr_uIoo ?_).1
          (intervalIntegrable_const (c := (0 : ℝ)))
        intro t ht
        rw [uIoo_of_le h1.le] at ht
        simp only
        rw [if_neg (fun h => by linarith [h.2, ht.2])]
        ring
      have hi2 : IntervalIntegrable (fun t =>
          deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
            (if 0 < γ ∧ γ ≤ t then m else 0)) volume γ T := by
        refine (intervalIntegrable_congr_uIoo ?_).1
          ((sp_ac δ γ T).intervalIntegrable_deriv.mul_const m)
        intro t ht
        rw [uIoo_of_le hγ] at ht
        simp only
        rw [if_pos ⟨h0, ht.1.le⟩]
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
      have e1 : (∫ t in (1 : ℝ)..γ,
          deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
            (if 0 < γ ∧ γ ≤ t then m else 0)) = 0 := by
        rw [intervalIntegral.integral_congr_uIoo (g := fun _ => (0 : ℝ))]
        · simp
        intro t ht
        rw [uIoo_of_le h1.le] at ht
        simp only
        rw [if_neg (fun h => by linarith [h.2, ht.2])]
        ring
      have e2 : (∫ t in γ..T,
          deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
            (if 0 < γ ∧ γ ≤ t then m else 0)) =
          ∫ t in γ..T,
            deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t * m := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hγ] at ht
        simp only
        rw [if_pos ⟨h0, ht.1⟩]
      rw [e1, e2, intervalIntegral.integral_mul_const, (sp_ac δ γ T).integral_deriv_eq_sub,
        if_pos ⟨h0, hγ⟩, if_neg (fun h => by linarith [h.2]), if_pos h1]
      ring
  · have hI : (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (if 0 < γ ∧ γ ≤ t then m else 0)) = 0 := by
      simp [h0]
    rw [hI, if_neg (fun h => h0 h.1), if_neg (fun h => h0 h.1), if_neg (by linarith)]
    ring

/-- LEAF: proof of book Lemma 16.9, page 431, the first integration by parts
`∑_{1 < γ ≤ T} f(γ) = ∫_{1+}^{T} f dN = f(T) N(T) - f(1) N(1) - ∫_1^T f'(t) N(t) dt` for
`f t = G t`, the norm of `G_δ (1/2 + i t)` as in the proof of Lemma 16.10, page 433.  Under
`hzeros` each summand `‖mellinMassTerm χ δ ρ‖` is the multiplicity of `ρ` times `G (im ρ)`.
`G` is Lipschitz on `[1, T]`, so it is absolutely continuous there.  Class HARD. -/
theorem stieltjes_sum_by_parts_N (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) -
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ *
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ (1 : ℝ)},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) -
      ∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) := by
  classical
  have hZmem : ∀ ρ : ℂ, ρ ∈ (sp_zeros_finite χ T).toFinset ↔
      (DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) := by
    intro ρ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have h1 : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ =
        (fun z : ℂ => if 1 < z.im then
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (z.im : ℝ) * Complex.I)‖ else 0) ρ.val := by
    rintro ⟨ρ, hρ⟩
    have hre := hzeros ρ hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2
    have hρeq : (1 / 2 : ℂ) + (ρ.im : ℝ) * Complex.I = ρ := by
      apply Complex.ext <;> simp [hre]
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with h
    · rw [hρeq, mellinMassTerm, norm_mul, norm_norm, Real.norm_natCast]
    · rfl
  rw [tsum_congr h1]
  rw [show (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        (fun z : ℂ => if 1 < z.im then
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (z.im : ℝ) * Complex.I)‖ else 0) ρ.val) =
      ∑' z : ℂ, Set.indicator {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
        (fun z : ℂ => if 1 < z.im then
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (z.im : ℝ) * Complex.I)‖ else 0) z from
      tsum_subtype {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
        (fun z : ℂ => if 1 < z.im then
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) *
            ‖gaussianMellin δ ((1 / 2 : ℂ) + (z.im : ℝ) * Complex.I)‖ else 0)]
  rw [tsum_eq_sum (s := (sp_zeros_finite χ T).toFinset)]
  swap
  · intro ρ hρ
    rw [Set.indicator_of_notMem]
    intro h
    exact hρ ((hZmem ρ).2 h)
  rw [Finset.sum_congr rfl (fun ρ hρ => Set.indicator_of_mem
    (show ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} from (hZmem ρ).1 hρ) _)]
  rw [sp_N_eq χ T (le_refl T), sp_N_eq χ T hT]
  have hI : (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ))) =
      ∑ ρ ∈ (sp_zeros_finite χ T).toFinset, ∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (if 0 < ρ.im ∧ ρ.im ≤ t then
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) else 0) := by
    rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT] at ht
      simp only
      rw [sp_N_eq χ T ht.2, Finset.mul_sum]
    · intro ρ _
      refine sp_int_mul_mono δ T hT ?_ ?_
      · intro s _ t _ hst
        exact sp_ite_mono _ _ _ _ (Nat.cast_nonneg _) hst
      · intro t _
        split_ifs
        · exact Nat.cast_nonneg _
        · exact le_rfl
  rw [hI, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  exact (sp_term δ T ρ.im _ hT (abs_le.1 ((hZmem ρ).1 hρ).2.2.2).2).symm

/-- LEAF: proof of book Lemma 16.9, page 431, the fact used to absorb the constant shift `c`:
`∫_1^T f'(t) dt = f(T) - f(1)` for `f t = G t`, the norm of `G_δ (1/2 + i t)`, which is
Lipschitz on `[1, T]` as the norm of a function holomorphic near the segment.  Class MEDIUM. -/
theorem norm_gaussianMellin_ftc (δ T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t) =
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ -
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ := by
  exact (sp_ac δ 1 T).integral_deriv_eq_sub

/-- LEAF: proof of book Lemma 16.9, page 431, the second integration by parts
`∫_1^T f'(t) M(t) dt = f(T) M(T) - f(1) M(1) - ∫_1^T f(t) M'(t) dt` with
`M'(t) = (1 / 2 π) log (q t / 2 π)`, for `f t = G t`.  Class MEDIUM. -/
theorem main_term_by_parts (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) =
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
          (T / (2 * π) * log ((q : ℝ) * T / (2 * π * exp 1))) -
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ *
          ((1 : ℝ) / (2 * π) * log ((q : ℝ) * (1 : ℝ) / (2 * π * exp 1))) -
        (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π))) := by
  have hF := sp_ac δ 1 T
  have hMac := (sp_M_contDiffOn q hT).absolutelyContinuousOnInterval
  have key := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hMac hF
  have e1 : (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) =
      ∫ t in (1 : ℝ)..T, (fun u : ℝ => u / (2 * π) * log ((q : ℝ) * u / (2 * π * exp 1))) t *
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    ring
  have e2 : (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => u / (2 * π) * log ((q : ℝ) * u / (2 * π * exp 1))) t *
          (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t) =
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    simp only
    rw [(sp_M_hasDerivAt q (by linarith [ht.1] : (0 : ℝ) < t)).deriv]
    ring
  rw [e1, key, e2]
  ring

/-- LEAF: regularity in the proof of book Lemma 16.9, page 431: on `[1, T]` the functions
`f' N`, `f'` and `f' M` are integrable, for `f t = G t` Lipschitz and `N` monotone and bounded,
so the integral of `f' (N + c - M)` splits linearly.  Class MEDIUM. -/
theorem stieltjes_integrability (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    IntervalIntegrable (fun t : ℝ =>
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)))
        MeasureTheory.volume 1 T ∧
      IntervalIntegrable (fun t : ℝ =>
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t)
        MeasureTheory.volume 1 T ∧
      IntervalIntegrable (fun t : ℝ =>
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1))))
        MeasureTheory.volume 1 T := by
  have hF := sp_ac δ 1 T
  refine ⟨?_, hF.intervalIntegrable_deriv,
    hF.intervalIntegrable_deriv.mul_continuousOn (sp_M_contDiffOn q hT).continuousOn⟩
  refine sp_int_mul_mono δ T hT (sp_N_mono χ T) ?_
  intro t _
  exact tsum_nonneg fun _ => Nat.cast_nonneg _

end LeanLab.HelfgottMajor.Decomp431a
