import LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral_stieltjes
import LeanLab.HelfgottMajor.Continuation457

/-!
Faithful split of the HARD leaf `stieltjes_positive_zero_sum` of
`LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral_stieltjes`: the Stieltjes
integration by parts in the proof of book Lemma 16.9, display 16.20, pages 431 and 432 of P0014
Part IV, applied as in the proof of Lemma 16.10, page 433, with `y = 1` and
`f t = |G_δ (1/2 + i t)|` on `[1, T]`.

Pieces:
* `mass_term_norm_eq`, PROVED: on the critical line the summand `‖mellinMassTerm χ δ ρ‖` is the
  multiplicity of `ρ` times `f (im ρ)`.
* `zeros_finite`, PROVED: under `hzeros` the zeros with `0 < re < 1` and `|im| ≤ T` form
  a finite set, so all sums over zeros in the proof are finite sums.
* `abel_summation_finset`, the Abel summation `∑_{1 < γ ≤ T} f(γ) = f(T) N(T) - f(1) N(1) -
  ∫_1^T f' N` for a finite family of points with weights, stated for a general `f` that is the
  integral of `f'` on `[1, T]`.
* `gaussian_norm_regular`, PROVED: `f` is continuous on `[1, T]` and has derivative
  `deriv f` off a countable set, with `deriv f` integrable, which gives the fundamental theorem
  of calculus with `deriv`.
* `hasDerivAt_main_term`, PROVED: `M'(t) = (1 / 2 π) log (q t / 2 π)` for
  `M t = t / (2 π) log (q t / (2 π e))`.
* `stieltjes_positive_zero_sum_of_leaves`: the assembly, the exact statement of the parent, PROVED
  with no gap in this file.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- Proof of Lemma 16.10, page 433: on the critical line `ρ = 1/2 + i γ`, the summand
`m(ρ) |G_δ(ρ)|` of display 16.20 is the multiplicity times `f(γ) = |G_δ(1/2 + i γ)|`.
Proved. -/
theorem mass_term_norm_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ) (ρ : ℂ)
    (h : ρ.re = 1 / 2) :
    ‖mellinMassTerm χ δ ρ‖ = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) *
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ρ.im : ℝ) * Complex.I)‖ := by
  have hρ : (1 / 2 : ℂ) + (ρ.im : ℝ) * Complex.I = ρ := by
    apply Complex.ext <;> simp [h]
  rw [hρ, mellinMassTerm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Proved, was LEAF MEDIUM. Proof of book Lemma 16.9, display 16.20, page 431: the sum over the nontrivial zeros
`ρ` with `|im ρ| ≤ T` is a finite sum, which the book uses tacitly when it writes it as the
Stieltjes integral `∫ f dN`.  Under `hzeros` these zeros lie on the compact segment
`1/2 + i [-T, T]`, inside the region `s ≠ 1` where `L(s, χ)` is analytic, and `L(s, χ)` does not
vanish for `re s > 1`, so by the identity theorem the zeros cannot accumulate. -/
theorem zeros_finite (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite := by
  set L := DirichletCharacter.LFunction χ with hLdef
  set V : Set ℂ := {1}ᶜ with hVdef
  have hVo : IsOpen V := isOpen_compl_singleton
  have hVc : IsPreconnected V :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (1 : ℂ)).isPreconnected
  have hLd : DifferentiableOn ℂ L V := fun s hs =>
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have hLa : AnalyticOnNhd ℂ L V := hLd.analyticOnNhd hVo
  rcases hLa.eqOn_zero_or_eventually_ne_zero_of_preconnected hVc with h0 | hne
  · exfalso
    have h2 : (2 : ℂ) ∈ V := by
      simp only [V, Set.mem_compl_iff, Set.mem_singleton_iff]
      norm_num
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
      (by norm_num) (h0 h2)
  · set K : Set ℂ := (fun u : ℝ => (1 / 2 : ℂ) + (u : ℝ) * Complex.I) '' Set.Icc (-T) T
    have hKc : IsCompact K := (isCompact_Icc).image (by fun_prop)
    have hKV : K ⊆ V := by
      rintro _ ⟨u, _, rfl⟩ h
      have := congrArg Complex.re (Set.mem_singleton_iff.1 h)
      norm_num at this
    have hfinK : (K \ {s | L s ≠ 0}).Finite :=
      hKc.finite_sdiff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hKV hne)
    refine hfinK.subset ?_
    rintro ρ ⟨h1, h2, h3, h4⟩
    have hre := hzeros ρ h1 h2 h3 h4
    refine ⟨⟨ρ.im, abs_le.1 h4, ?_⟩, by simpa using h1⟩
    apply Complex.ext <;> simp [hre]

/-- One point of the Abel summation of the proof of Lemma 16.9, display 16.20, page 431:
for a single point `γ` of unit weight, `[1 < γ ≤ T] f(γ) = f(T) N(T) - f(1) N(1) - ∫_1^T f' N`
with `N(t) = [0 < γ ≤ t]`.  Proved. -/
theorem abel_single (γ : ℝ) (f f' : ℝ → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (hf' : IntervalIntegrable f' volume 1 T)
    (hftc : ∀ x ∈ Set.Icc (1 : ℝ) T, ∫ t in (1 : ℝ)..x, f' t = f x - f 1) :
    IntervalIntegrable (fun t => f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0)) volume 1 T ∧
    (if 1 < γ ∧ γ ≤ T then f γ else 0) =
      f T * (if 0 < γ ∧ γ ≤ T then (1 : ℝ) else 0) -
      f 1 * (if 0 < γ ∧ γ ≤ 1 then (1 : ℝ) else 0) -
      ∫ t in (1 : ℝ)..T, f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0) := by
  have hint : IntervalIntegrable (fun t => f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0))
      volume 1 T := by
    have hm : MeasurableSet {t : ℝ | 0 < γ ∧ γ ≤ t} :=
      (MeasurableSet.const (0 < γ)).inter measurableSet_Ici
    have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hf'
    have h2 := h1.indicator hm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  refine ⟨hint, ?_⟩
  by_cases h0 : 0 < γ
  swap
  · have hn : ¬ (1 < γ ∧ γ ≤ T) := fun h => h0 (lt_trans one_pos h.1)
    simp [h0, hn]
  by_cases h1 : γ ≤ 1
  · have hc : ∫ t in (1 : ℝ)..T, f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0) =
        ∫ t in (1 : ℝ)..T, f' t := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le hT] at ht
      have : γ ≤ t := h1.trans ht.1
      simp [h0, this]
    rw [hc, hftc T ⟨hT, le_rfl⟩]
    have hn : ¬ (1 < γ ∧ γ ≤ T) := fun h => absurd h.1 (not_lt.2 h1)
    simp [h0, h1, h1.trans hT]
  push Not at h1
  by_cases h2 : γ ≤ T
  · have hsub1 : IntervalIntegrable (fun t => f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0))
        volume 1 γ := hint.mono_set (by
          rw [Set.uIcc_of_le hT, Set.uIcc_of_le h1.le]
          exact Set.Icc_subset_Icc le_rfl h2)
    have hsub2 : IntervalIntegrable (fun t => f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0))
        volume γ T := hint.mono_set (by
          rw [Set.uIcc_of_le hT, Set.uIcc_of_le h2]
          exact Set.Icc_subset_Icc h1.le le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals hsub1 hsub2]
    have hA : ∫ t in (1 : ℝ)..γ, f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0) = 0 := by
      have : ∫ t in (1 : ℝ)..γ, f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0) =
          ∫ t in (1 : ℝ)..γ, (0 : ℝ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [(Set.countable_singleton γ).ae_notMem volume] with t ht htI
        rw [Set.uIoc_of_le h1.le] at htI
        have hlt : t < γ := lt_of_le_of_ne htI.2 (by simpa using ht)
        simp [not_le.2 hlt]
      rw [this, intervalIntegral.integral_zero]
    have hB : ∫ t in γ..T, f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0) =
        ∫ t in γ..T, f' t := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le h2] at ht
      simp [h0, ht.1]
    have hfγ : IntervalIntegrable f' volume 1 γ := hf'.mono_set (by
          rw [Set.uIcc_of_le hT, Set.uIcc_of_le h1.le]
          exact Set.Icc_subset_Icc le_rfl h2)
    rw [hA, hB, ← intervalIntegral.integral_interval_sub_left hf' hfγ, hftc T ⟨hT, le_rfl⟩,
      hftc γ ⟨h1.le, h2⟩]
    simp [h0, h1, h2, not_le.2 h1]
  · push Not at h2
    have hc : ∫ t in (1 : ℝ)..T, f' t * (if 0 < γ ∧ γ ≤ t then (1 : ℝ) else 0) =
        ∫ t in (1 : ℝ)..T, (0 : ℝ) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le hT] at ht
      have : ¬ γ ≤ t := not_le.2 (lt_of_le_of_lt ht.2 h2)
      simp [this]
    rw [hc, intervalIntegral.integral_zero]
    simp [not_le.2 h2, not_le.2 (lt_of_le_of_lt hT h2)]

/-- The Abel summation of the proof of Lemma 16.9, display 16.20, page 431, for a finite family
of points `γ a` with weights `w a` and a function `f` that is the integral of `f'` on `[1, T]`:
`∑_{1 < γ ≤ T} w f(γ) = f(T) N(T) - f(1) N(1) - ∫_1^T f' N` with `N(t) = ∑_{0 < γ ≤ t} w`,
together with the integrability of `f' N`.  Proved. -/
theorem abel_summation_finset {α : Type*} (Z : Finset α) (γ w : α → ℝ) (f f' : ℝ → ℝ)
    (T : ℝ) (hT : 1 ≤ T) (hf' : IntervalIntegrable f' volume 1 T)
    (hftc : ∀ x ∈ Set.Icc (1 : ℝ) T, ∫ t in (1 : ℝ)..x, f' t = f x - f 1) :
    IntervalIntegrable (fun t => f' t * ∑ a ∈ Z, if 0 < γ a ∧ γ a ≤ t then w a else 0)
        volume 1 T ∧
    ∑ a ∈ Z, (if 1 < γ a ∧ γ a ≤ T then w a * f (γ a) else 0) =
      f T * (∑ a ∈ Z, if 0 < γ a ∧ γ a ≤ T then w a else 0) -
      f 1 * (∑ a ∈ Z, if 0 < γ a ∧ γ a ≤ 1 then w a else 0) -
      ∫ t in (1 : ℝ)..T, f' t * ∑ a ∈ Z, if 0 < γ a ∧ γ a ≤ t then w a else 0 := by
  have hS := fun a => abel_single (γ a) f f' T hT hf' hftc
  have hfun : (fun t => f' t * ∑ a ∈ Z, if 0 < γ a ∧ γ a ≤ t then w a else 0) =
      fun t => ∑ a ∈ Z, w a * (f' t * (if 0 < γ a ∧ γ a ≤ t then (1 : ℝ) else 0)) := by
    funext t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    split_ifs <;> ring
  have hI : ∀ a ∈ Z, IntervalIntegrable
      (fun t => w a * (f' t * (if 0 < γ a ∧ γ a ≤ t then (1 : ℝ) else 0))) volume 1 T :=
    fun a _ => (hS a).1.const_mul (w a)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    have := IntervalIntegrable.sum Z hI
    convert this using 1
    funext t
    simp
  · rw [hfun, intervalIntegral.integral_finsetSum hI, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [intervalIntegral.integral_const_mul]
    have h := (hS a).2
    have e1 : (if 1 < γ a ∧ γ a ≤ T then w a * f (γ a) else 0) =
        w a * (if 1 < γ a ∧ γ a ≤ T then f (γ a) else 0) := by split_ifs <;> ring
    have e2 : ∀ x : ℝ, (if 0 < γ a ∧ γ a ≤ x then w a else 0) =
        w a * (if 0 < γ a ∧ γ a ≤ x then (1 : ℝ) else 0) := fun x => by split_ifs <;> ring
    rw [e1, e2, e2, h]
    ring

/-- Proved, was LEAF MEDIUM. Proof of Lemma 16.10, page 433, the regularity of `f t = |G_δ (1/2 + i t)|` on
`[1, T]` that Lemma 16.9 needs for its integrations by parts: `f` is continuous on `[1, T]`,
differentiable with derivative `deriv f` off a countable set, the zeros of `G_δ` on the line,
and `deriv f` is integrable, being bounded by `|G_δ'|`.  It rests on
`Continuation457.gaussian_mellin_differentiable`, the holomorphy of `G_δ` on `re s > 0`. -/
theorem gaussian_norm_regular (δ T : ℝ) (hT : 1 ≤ T) :
    ∃ S : Set ℝ, S.Countable ∧
      ContinuousOn (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖)
        (Set.Icc 1 T) ∧
      (∀ x ∈ Set.Ioo (1 : ℝ) T \ S,
        HasDerivAt (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖)
          (deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) x) x) ∧
      IntervalIntegrable
        (deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖))
        volume 1 T := by
  set G := gaussianMellin δ with hGdef
  set g : ℝ → ℂ := fun u => G ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) with hgdef
  set f : ℝ → ℝ := fun u => ‖G ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖ with hfdef
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hGd : DifferentiableOn ℂ G U := fun s hs =>
    (Continuation457.gaussian_mellin_differentiable δ s hs).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ G U := hGd.analyticOnNhd hUo
  have hline : ∀ u : ℝ, (1 / 2 : ℂ) + (u : ℝ) * Complex.I ∈ U := fun u => by
    simp [U]
  have hgd : ∀ u : ℝ, HasDerivAt g (deriv G ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) * Complex.I) u :=
    fun u => by
      have h1 : HasDerivAt (fun s : ℂ => (1 / 2 : ℂ) + s * Complex.I) Complex.I (u : ℂ) := by
        simpa using ((hasDerivAt_id (u : ℂ)).mul_const Complex.I).const_add (1 / 2 : ℂ)
      have h2 := ((hGd _ (hline u)).differentiableAt (hUo.mem_nhds (hline u))).hasDerivAt
      exact (h2.comp (u : ℂ) h1).comp_ofReal
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun u => (hgd u).continuousAt
  have hfc : Continuous f := continuous_norm.comp hgc
  -- the derivative of `f` is bounded near `[1, T]`
  have hG'c : ContinuousOn (deriv G) U := hGa.deriv.continuousOn
  have hg'c : Continuous (fun u : ℝ => deriv G ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) * Complex.I) := by
    refine Continuous.mul ?_ continuous_const
    refine hG'c.comp_continuous (by fun_prop) hline
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T + 1)).exists_bound_of_continuousOn
    hg'c.continuousOn
  have hlip : LipschitzOnWith (Real.toNNReal C) g (Set.Icc 0 (T + 1)) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => (hgd x).differentiableAt)
      (fun x hx => ?_) (convex_Icc _ _)
    rw [(hgd x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact (hC x hx).trans (le_max_left _ _)
  have hlipf : LipschitzOnWith (Real.toNNReal C) f (Set.Icc 0 (T + 1)) := by
    have := (LipschitzWith.comp_lipschitzOnWith (lipschitzWith_one_norm (E := ℂ)) hlip)
    rw [one_mul] at this
    exact this
  have hbd : ∀ x ∈ Set.Ioo (0 : ℝ) (T + 1), ‖deriv f x‖ ≤ Real.toNNReal C := fun x hx =>
    norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hx.1 hx.2) hlipf
  have hint : IntervalIntegrable (deriv f) volume 1 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    refine Integrable.mono' (g := fun _ => (Real.toNNReal C : ℝ))
      (integrableOn_const (measure_Ioc_lt_top).ne) (measurable_deriv f).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
    exact hbd x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- the zero set on the segment
  rcases hGa.eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected with h0 | hne
  · have hf0 : f = fun _ => 0 := by
      funext u
      simp only [f]
      rw [h0 (hline u)]
      simp
    refine ⟨∅, Set.countable_empty, hfc.continuousOn, fun x _ => ?_, hint⟩
    rw [hf0]
    simpa using hasDerivAt_const x (0 : ℝ)
  · set K : Set ℂ := (fun u : ℝ => (1 / 2 : ℂ) + (u : ℝ) * Complex.I) '' Set.Icc 1 T
    have hKc : IsCompact K := (isCompact_Icc).image (by fun_prop)
    have hKU : K ⊆ U := by
      rintro _ ⟨u, _, rfl⟩
      exact hline u
    have hfinK : (K \ {s | G s ≠ 0}).Finite :=
      hKc.finite_sdiff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hKU hne)
    set S : Set ℝ := {u | u ∈ Set.Icc 1 T ∧ g u = 0}
    have hinj : Set.InjOn (fun u : ℝ => (1 / 2 : ℂ) + (u : ℝ) * Complex.I) S := by
      intro a _ b _ hab
      have := congrArg Complex.im hab
      simpa using this
    have hSfin : S.Finite := by
      refine Set.Finite.of_finite_image (hfinK.subset ?_) hinj
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu.1, rfl⟩, by simpa [g] using hu.2⟩
    refine ⟨S, hSfin.countable, hfc.continuousOn, fun x hx => ?_, hint⟩
    have hgx : g x ≠ 0 := fun h => hx.2 ⟨⟨hx.1.1.le, hx.1.2.le⟩, h⟩
    exact ((hgd x).differentiableAt.norm ℂ hgx).hasDerivAt

/-- Proof of Lemma 16.9, page 431: the main term `M(t) = (t / 2 π) log (q t / 2 π e)` of the
zero count has derivative `M'(t) = (1 / 2 π) log (q t / 2 π)`.  Proved. -/
theorem hasDerivAt_main_term (q : ℕ) [NeZero q] (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))
      (1 / (2 * π) * log ((q : ℝ) * t / (2 * π))) t := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hpos : 0 < (q : ℝ) * t / (2 * π * exp 1) := by positivity
  have h1 : HasDerivAt (fun t : ℝ => (q : ℝ) * t / (2 * π * exp 1))
      ((q : ℝ) * 1 / (2 * π * exp 1)) t :=
    ((hasDerivAt_id t).const_mul (q : ℝ)).div_const (2 * π * exp 1)
  have h2 := h1.log hpos.ne'
  have h3 := ((hasDerivAt_id t).div_const (2 * π)).mul h2
  refine h3.congr_deriv ?_
  have hl : log ((q : ℝ) * t / (2 * π * exp 1)) = log ((q : ℝ) * t / (2 * π)) - 1 := by
    rw [show (q : ℝ) * t / (2 * π * exp 1) = (q : ℝ) * t / (2 * π) / exp 1 by
      field_simp, Real.log_div (by positivity) (exp_pos 1).ne', Real.log_exp]
  simp only [id]
  rw [hl]
  field_simp
  ring

/-- Sums over zeros as finite sums over the finite zero set `Z` of `zeros_finite`. -/
theorem tsum_subtype_eq_sum (Z : Finset ℂ) (P : ℂ → Prop) (g : ℂ → ℝ)
    (hP : ∀ ρ, P ρ → ρ ∈ Z) :
    (∑' ρ : {ρ : ℂ // P ρ}, g ρ.val) = ∑ ρ ∈ Z, Set.indicator {ρ | P ρ} g ρ := by
  rw [show (∑' ρ : {ρ : ℂ // P ρ}, g ρ.val) = ∑' ρ : ({ρ | P ρ} : Set ℂ), g ρ from rfl,
    tsum_subtype {ρ | P ρ} g]
  refine tsum_eq_sum (fun ρ hρ => ?_)
  rw [Set.indicator_of_notMem]
  exact fun h => hρ (hP ρ h)

/-- Assembly of the split: the exact statement of `stieltjes_positive_zero_sum`, proved from
`zeros_finite`, `gaussian_norm_regular` and the Abel summation, with no gap. -/
theorem stieltjes_positive_zero_sum_of_leaves (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T c : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
        ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
          T / (2 * π) * log ((q : ℝ) * T / (2 * π * exp 1))) -
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ *
        ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ (1 : ℝ)},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
          (1 : ℝ) / (2 * π) * log ((q : ℝ) * (1 : ℝ) / (2 * π * exp 1))) -
      (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
            t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) := by
  classical
  set f : ℝ → ℝ := fun u => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖ with hfdef
  set f' : ℝ → ℝ := deriv f with hf'def
  set M : ℝ → ℝ := fun t => t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)) with hMdef
  set L := DirichletCharacter.LFunction χ with hLdef
  set m : ℂ → ℝ := fun ρ => (analyticOrderNatAt L ρ : ℝ) with hmdef
  -- the finite zero set
  have hfin := zeros_finite q χ T hzeros
  set Z := hfin.toFinset with hZdef
  have hZ : ∀ ρ, ρ ∈ Z ↔ (L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) := fun ρ => by
    simp [Z, L]
  -- regularity and the fundamental theorem of calculus
  obtain ⟨S, hS, hcont, hderiv, hf'int⟩ := gaussian_norm_regular δ T hT
  have hftc : ∀ x ∈ Set.Icc (1 : ℝ) T, ∫ t in (1 : ℝ)..x, f' t = f x - f 1 := by
    intro x hx
    refine integral_eq_of_hasDerivAt_off_countable_of_le f f' hx.1 hS
      (hcont.mono (Set.Icc_subset_Icc le_rfl hx.2)) (fun y hy => hderiv y ⟨?_, hy.2⟩) ?_
    · exact ⟨hy.1.1, lt_of_lt_of_le hy.1.2 hx.2⟩
    · exact hf'int.mono_set (by
        rw [Set.uIcc_of_le hT, Set.uIcc_of_le hx.1]
        exact Set.Icc_subset_Icc le_rfl hx.2)
  -- Abel summation with points `im ρ` and weights the multiplicities
  obtain ⟨hNint, hAbel⟩ := abel_summation_finset Z (fun ρ => ρ.im) m f f' T hT hf'int hftc
  -- the counts as finite sums
  have hN : ∀ t, t ≤ T →
      (∑' ρ : {ρ : ℂ // L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t}, m ρ.val) =
        ∑ ρ ∈ Z, if 0 < ρ.im ∧ ρ.im ≤ t then m ρ else 0 := by
    intro t ht
    rw [tsum_subtype_eq_sum Z _ m (fun ρ h => (hZ ρ).2 ⟨h.1, h.2.1, h.2.2.1,
      abs_le.2 ⟨by linarith [h.2.2.2.1, hT], h.2.2.2.2.trans ht⟩⟩)]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    obtain ⟨h1, h2, h3, _⟩ := (hZ ρ).1 hρ
    simp [Set.indicator_apply, h1, h2, h3]
  -- the left side as a finite sum
  have hLHS : (∑' ρ : {ρ : ℂ // L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      ∑ ρ ∈ Z, (if 1 < ρ.im ∧ ρ.im ≤ T then m ρ * f ρ.im else 0) := by
    have hpt : ∀ ρ : {ρ : ℂ // L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ =
          (fun ρ : ℂ => if 1 < ρ.im ∧ ρ.im ≤ T then m ρ * f ρ.im else 0) ρ.val := by
      intro ρ
      obtain ⟨h1, h2, h3, h4⟩ := ρ.2
      have hre := hzeros ρ.val h1 h2 h3 h4
      have hle : ρ.val.im ≤ T := (le_abs_self _).trans h4
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hle, and_true]
      split_ifs
      · exact mass_term_norm_eq q χ δ ρ.val hre
      · rfl
    rw [tsum_congr hpt, tsum_subtype_eq_sum Z
      (fun ρ => L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T)
      (fun ρ : ℂ => if 1 < ρ.im ∧ ρ.im ≤ T then m ρ * f ρ.im else 0) (fun ρ h => (hZ ρ).2 h)]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    rw [Set.indicator_of_mem]
    exact (hZ ρ).1 hρ
  -- integration by parts against the main term
  have hMd : ∀ t, 0 < t → HasDerivAt M (1 / (2 * π) * log ((q : ℝ) * t / (2 * π))) t :=
    fun t ht => hasDerivAt_main_term q t ht
  have hMcont : ContinuousOn M (Set.Icc 1 T) := fun t ht =>
    (hMd t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hM'cont : ContinuousOn (fun t : ℝ => 1 / (2 * π) * log ((q : ℝ) * t / (2 * π)))
      (Set.Icc 1 T) := by
    have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    refine continuousOn_const.mul (ContinuousOn.log (by fun_prop) (fun t ht => ?_))
    have : 0 < t := by linarith [ht.1]
    positivity
  have hfM'int : IntervalIntegrable
      (fun t => f t * (1 / (2 * π) * log ((q : ℝ) * t / (2 * π)))) volume 1 T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hT]
    exact hcont.mul hM'cont
  have hf'Mint : IntervalIntegrable (fun t => f' t * M t) volume 1 T := by
    refine hf'int.mul_continuousOn ?_
    rw [Set.uIcc_of_le hT]
    exact hMcont
  have hIBP : ∫ t in (1 : ℝ)..T,
      (f' t * M t + f t * (1 / (2 * π) * log ((q : ℝ) * t / (2 * π)))) =
        f T * M T - f 1 * M 1 := by
    refine integral_eq_of_hasDerivAt_off_countable_of_le (fun t => f t * M t) _ hT hS
      (hcont.mul hMcont) (fun x hx => ?_) (hf'Mint.add hfM'int)
    exact (hderiv x hx).mul (hMd x (by linarith [hx.1.1]))
  rw [intervalIntegral.integral_add hf'Mint hfM'int] at hIBP
  -- the error integral split into three pieces
  have hErr : (∫ t in (1 : ℝ)..T, f' t *
      ((∑' ρ : {ρ : ℂ // L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t}, m ρ.val) + c
        - M t)) =
      (∫ t in (1 : ℝ)..T, f' t * ∑ ρ ∈ Z, if 0 < ρ.im ∧ ρ.im ≤ t then m ρ else 0) +
        c * (f T - f 1) - ∫ t in (1 : ℝ)..T, f' t * M t := by
    have hc : (∫ t in (1 : ℝ)..T, f' t *
        ((∑' ρ : {ρ : ℂ // L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t}, m ρ.val) + c
          - M t)) =
        ∫ t in (1 : ℝ)..T, ((f' t * ∑ ρ ∈ Z, if 0 < ρ.im ∧ ρ.im ≤ t then m ρ else 0) +
          c * f' t - f' t * M t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le hT] at ht
      rw [hN t ht.2]
      ring
    rw [hc, intervalIntegral.integral_sub (hNint.add (hf'int.const_mul c)) hf'Mint,
      intervalIntegral.integral_add hNint (hf'int.const_mul c),
      intervalIntegral.integral_const_mul, hftc T ⟨hT, le_rfl⟩]
  have hfT : f T = ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ := rfl
  have hf1 : f 1 = ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ := rfl
  have hint1 : (∫ t in (1 : ℝ)..T,
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ * log ((q : ℝ) * t / (2 * π))) =
      ∫ t in (1 : ℝ)..T, f t * log ((q : ℝ) * t / (2 * π)) := rfl
  have hint2 : (∫ t in (1 : ℝ)..T, f t * (1 / (2 * π) * log ((q : ℝ) * t / (2 * π)))) =
      (1 / (2 * π)) * ∫ t in (1 : ℝ)..T, f t * log ((q : ℝ) * t / (2 * π)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  change _ = (1 / (2 * π)) * (∫ t in (1 : ℝ)..T, f t * log ((q : ℝ) * t / (2 * π))) +
      f T * ((∑' ρ : {ρ : ℂ // L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
            m ρ.val) + c - M T) -
      f 1 * ((∑' ρ : {ρ : ℂ // L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ (1 : ℝ)},
            m ρ.val) + c - M 1) -
      (∫ t in (1 : ℝ)..T, f' t *
        ((∑' ρ : {ρ : ℂ // L ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t}, m ρ.val) + c
          - M t))
  rw [hErr, hLHS, hN T le_rfl, hN 1 hT, hAbel, ← hint2]
  linarith [hIBP]

end LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit

#print axioms LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit.mass_term_norm_eq
#print axioms LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit.abel_single
#print axioms LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit.abel_summation_finset
#print axioms LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit.hasDerivAt_main_term
#print axioms LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit.tsum_subtype_eq_sum
#print axioms LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit.zeros_finite
#print axioms LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit.gaussian_norm_regular
#print axioms LeanLab.HelfgottMajor.Decomp431a.StieltjesSplit.stieltjes_positive_zero_sum_of_leaves
