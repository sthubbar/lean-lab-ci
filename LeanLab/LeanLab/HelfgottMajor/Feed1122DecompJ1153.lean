import LeanLab.HelfgottMajor.DecompF1606

/-!
Feed burst 2026-11-22 for `DecompJ1153`.

All three open declarations of `DecompJ1153` already have splits on main:
`Decomp389b.middle_mass_bound` assembles `middle_mass_bound` with the identical statement,
`Decomp388a.inv_im_sum_bound` assembles `inv_im_sum_bound` from a zero count leaf that
`SPLIT_zero_count_explicit_upper` splits further, and `DecompF1606.gaussian_moment_sum_bound_F1606`
assembles `gaussian_moment_sum_bound` from the single open leaf `leaf_gaussian_moment_sum_le`.

This file splits that last open leaf. The height factor `|im ρ| ≤ T` is pulled out of the
zero sum, which is proved here, leaving a sampling inequality for the plain sum of
multiplicities times squared Mellin norms over the middle zeros, which is the one LEAF.
The parent `gaussian_moment_sum_bound` is then reassembled with its exact statement.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b DecompJ1153

/-- The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.
Copied from the private lemma of `DecompJ1153`, multiplier trick. -/
private theorem zeros_strip_finite_f (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite := by
  classical
  set K : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
  have hKc : IsCompact K := by
    have himg : K = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-T) T) := by
      ext z
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, abs_le.mp h3⟩, by apply Complex.ext <;> simp⟩
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨⟨h1, h2⟩, h3⟩ := hp
        exact ⟨by simpa using h1, by simpa using h2, by simpa using abs_le.mpr h3⟩
    rw [himg]
    exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  set g : ℂ → ℂ := if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q
    else fun s => (s - 1) * DirichletCharacter.LFunction χ s with hg
  have hg1 : χ = 1 → g = DirichletCharacter.LFunctionTrivChar₁ q := by
    intro h; rw [hg, if_pos h]
  have hg2 : χ ≠ 1 → g = fun s => (s - 1) * DirichletCharacter.LFunction χ s := by
    intro h; rw [hg, if_neg h]
  have hgd : Differentiable ℂ g := by
    by_cases h : χ = 1
    · rw [hg1 h]
      exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
    · rw [hg2 h]
      have h1' : Differentiable ℂ fun s : ℂ => s - 1 := by fun_prop
      exact h1'.mul (DirichletCharacter.differentiable_LFunction h)
  have hex : ∃ w, g w ≠ 0 := by
    by_cases h : χ = 1
    · refine ⟨1, ?_⟩
      rw [hg1 h]
      exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · refine ⟨2, ?_⟩
      rw [hg2 h]
      have h2 : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
        DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2) (Or.inl h) (by norm_num)
      exact mul_ne_zero (by norm_num) h2
  have hne : ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 → z.re < 1 → g z = 0 := by
    intro z hL h1
    by_cases h : χ = 1
    · have hz1 : z ≠ 1 := by
        rintro rfl
        rw [Complex.one_re] at h1
        exact absurd h1 (by norm_num)
      have hL1 : DirichletCharacter.LFunctionTrivChar q z = 0 := by
        have h' : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z = 0 := by
          rw [← h]; exact hL
        exact h'
      rw [hg1 h]
      simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1, hL1, mul_zero]
    · rw [hg2 h]
      simp only [hL, mul_zero]
  have hcod : g ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ :=
    AnalyticOnNhd.preimage_zero_mem_codiscrete (f := g)
      (hgd.differentiableOn.analyticOnNhd isOpen_univ) hex.choose_spec
  rw [Set.preimage_compl] at hcod
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcod
  refine Set.Finite.subset ((hKc.inter_right hclosed).finite (hdisc.mono Set.inter_subset_right)) ?_
  rintro z ⟨hL, h0, h1, him⟩
  exact ⟨⟨le_of_lt h0, le_of_lt h1, him⟩, hne z hL h1⟩

/-- Height pull out, proved: every zero counted in `gaussianMomentSum χ δ T` has
`|im ρ| ≤ T`, so the moment sum is at most `T` times the plain sum of multiplicities times
squared Mellin norms over the middle zeros `1 < |im ρ| ≤ T`. P0014 page 40, the step before
display 4.31. -/
theorem gaussian_moment_le_height_mul_sampled (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (_hT : 1 ≤ T) :
    gaussianMomentSum χ δ T ≤
      T * ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ := by
  classical
  set ι := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
    with hι
  have hfin := zeros_strip_finite_f q χ T
  haveI : Fintype ι := hι.symm ▸ hfin.fintype
  unfold gaussianMomentSum
  rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro ρ _
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs with h
  · have hle : |(ρ : ℂ).im| ≤ T := ρ.2.2.2.2
    have h0 : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) *
        ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2 := by positivity
    calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) * |(ρ : ℂ).im| *
          ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2
        = |(ρ : ℂ).im| * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) *
          ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2) := by ring
      _ ≤ T * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) *
          ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2) := mul_le_mul_of_nonneg_right hle h0
  · simp

/-- LEAF: P0014 pages 38 to 40, partial summation of display 4.31 against the zero count of
display 4.26, Lemma 4.3, then the Mellin Plancherel identity of display 4.42 on page 43, compare
book Part IV pages 433 and 434, display 16.26. HARD.
Sampling inequality: the sum over zeros with `1 < |im ρ| ≤ T` of multiplicity times the squared
Mellin norm of the Gaussian profile is at most `(nTwo + nLog) log (q T)`. Heuristic: the main
term is `∫ |G(1/2+it)|^2 log (q|t|/2π) / 2π dt`, at most `nTwo log (qT)` by Plancherel, and the
count error of display 4.26 is absorbed by the `nLog` part. Unlike the refuted
`leaf_moment_plancherel_bound`, the right side carries the factor `log (q T)`. -/
theorem leaf_middle_sampled_mass_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ ≤
      (Sec45.nTwo + Sec45.nLog) * log (q * T) := by
  sorry

/-- Exactly `DecompF1606.leaf_gaussian_moment_sum_le`, assembled from the proved height pull
out and the sampling LEAF. -/
theorem leaf_gaussian_moment_sum_le_feed1122 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    gaussianMomentSum χ δ T ≤ (Sec45.nTwo + Sec45.nLog) * T * log (q * T) := by
  have h1 := gaussian_moment_le_height_mul_sampled q χ δ T hT
  have h2 := leaf_middle_sampled_mass_le q χ hχ δ T hT hzeros
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  calc gaussianMomentSum χ δ T ≤ _ := h1
    _ ≤ T * ((Sec45.nTwo + Sec45.nLog) * log (q * T)) := mul_le_mul_of_nonneg_left h2 hT0
    _ = (Sec45.nTwo + Sec45.nLog) * T * log (q * T) := by ring

/-- Exactly `DecompJ1153.gaussian_moment_sum_bound`, assembled from
`leaf_gaussian_moment_sum_le_feed1122` and the proved square root facts of `DecompF1606`. -/
theorem gaussian_moment_sum_bound_feed1122 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    sqrt (gaussianMomentSum χ δ T) ≤
      (sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T) * sqrt (log (q * T)) := by
  have h1 := leaf_gaussian_moment_sum_le_feed1122 q χ hχ δ T hT hzeros
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have hsum_nonneg : 0 ≤ Sec45.nTwo + Sec45.nLog :=
    add_nonneg DecompF1606.leaf_nTwo_nonneg DecompF1606.leaf_nLog_nonneg
  calc sqrt (gaussianMomentSum χ δ T)
      ≤ sqrt ((Sec45.nTwo + Sec45.nLog) * T * log (q * T)) := Real.sqrt_le_sqrt h1
    _ = sqrt ((Sec45.nTwo + Sec45.nLog) * (T * log (q * T))) := by ring_nf
    _ = sqrt (Sec45.nTwo + Sec45.nLog) * sqrt (T * log (q * T)) :=
        Real.sqrt_mul hsum_nonneg _
    _ = sqrt (Sec45.nTwo + Sec45.nLog) * (sqrt T * sqrt (log (q * T))) := by
        rw [Real.sqrt_mul hT0 _]
    _ ≤ (sqrt Sec45.nTwo + sqrt Sec45.nLog) * (sqrt T * sqrt (log (q * T))) := by
        gcongr
        exact DecompF1606.leaf_sqrt_add_le _ _ DecompF1606.leaf_nTwo_nonneg
          DecompF1606.leaf_nLog_nonneg
    _ = (sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T) * sqrt (log (q * T)) := by ring_nf


end LeanLab.HelfgottMajor.Feed1122DecompJ1153
