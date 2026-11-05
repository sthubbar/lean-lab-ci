import LeanLab.HelfgottMajor.Decomp269b

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- The sum of 1/|ρ.im| over zeros with 1 < |ρ.im| ≤ T. -/
noncomputable def invImSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) / |ρ.val.im|) ρ

/-- The sum of |ρ.im| * ‖gaussianMellin δ ρ‖^2 over zeros with 1 < |ρ.im| ≤ T. -/
noncomputable def gaussianMomentSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * |ρ.val.im| * ‖gaussianMellin δ ρ.val‖^2) ρ

/-- The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.

Multiplier trick: `s ↦ (s - 1) * L χ s` is entire (for the trivial character the
pole-removed `LFunctionTrivChar₁` is used instead), it vanishes at every zero of `L χ`
inside the strip, and it is not identically zero. Hence its zero set is discrete, and a
closed bounded box meets it finitely. -/
private theorem zeros_strip_finite (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
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

/-- LEAF. Page 40, display 4.31. Cauchy-Schwarz inequality for sums over zeros. -/
theorem middle_mass_cauchy_schwarz (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    middleMass χ δ T ≤ sqrt (invImSum χ T) * sqrt (gaussianMomentSum χ δ T) := by
  classical
  set ι := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
    with hι
  have hfin : (Set.Finite {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ T}) := zeros_strip_finite q χ T
  haveI : Fintype ι := hι.symm ▸ hfin.fintype
  let a : ι → ℝ := fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ)
  let b : ι → ℝ := fun ρ => ‖gaussianMellin δ (ρ : ℂ)‖
  let m : ι → ℝ := fun ρ => max |(ρ : ℂ).im| 1
  let ind : ι → ℝ := fun ρ => if |(ρ : ℂ).im| ≤ 1 then 0 else 1
  have ha : ∀ ρ, 0 ≤ a ρ := fun ρ => Nat.cast_nonneg _
  have hb : ∀ ρ, 0 ≤ b ρ := fun ρ => norm_nonneg _
  have hm : ∀ ρ, 0 < m ρ := fun ρ => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hind : ∀ ρ, 0 ≤ ind ρ := by
    intro ρ; simp only [ind]; split <;> norm_num
  have hM : middleMass χ δ T = ∑ ρ : ι, ind ρ * (a ρ * b ρ) := by
    simp only [middleMass]
    rw [tsum_fintype]
    refine Finset.sum_congr rfl ?_
    intro ρ _
    show Set.indicator {ρ : ι | |(ρ : ℂ).im| ≤ 1}ᶜ (fun ρ => mellinMassTerm χ δ (ρ : ℂ)) ρ
      = ind ρ * (a ρ * b ρ)
    rw [Set.indicator_apply]
    by_cases h : |(ρ : ℂ).im| ≤ 1
    · rw [if_neg (by simp [h])]
      simp [ind, h]
    · rw [if_pos (by simp [h])]
      simp [ind, h, a, b, mellinMassTerm]
  have hI : invImSum χ T = ∑ ρ : ι, ind ρ * (a ρ / m ρ) := by
    simp only [invImSum]
    rw [tsum_fintype]
    refine Finset.sum_congr rfl ?_
    intro ρ _
    show Set.indicator {ρ : ι | |(ρ : ℂ).im| ≤ 1}ᶜ
      (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) / |(ρ : ℂ).im|) ρ
      = ind ρ * (a ρ / m ρ)
    rw [Set.indicator_apply]
    by_cases h : |(ρ : ℂ).im| ≤ 1
    · rw [if_neg (by simp [h])]
      simp [ind, h]
    · rw [if_pos (by simp [h])]
      have hgt : (1 : ℝ) ≤ |(ρ : ℂ).im| := le_of_lt (not_le.mp h)
      have hmv : m ρ = |(ρ : ℂ).im| := by simp only [m]; exact max_eq_left hgt
      simp [ind, h, a, hmv]
  have hG : gaussianMomentSum χ δ T
      = ∑ ρ : ι, ind ρ * (a ρ * m ρ * (b ρ) ^ 2) := by
    simp only [gaussianMomentSum]
    rw [tsum_fintype]
    refine Finset.sum_congr rfl ?_
    intro ρ _
    show Set.indicator {ρ : ι | |(ρ : ℂ).im| ≤ 1}ᶜ
      (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) * |(ρ : ℂ).im| *
        ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2) ρ = ind ρ * (a ρ * m ρ * (b ρ) ^ 2)
    rw [Set.indicator_apply]
    by_cases h : |(ρ : ℂ).im| ≤ 1
    · rw [if_neg (by simp [h])]
      simp [ind, h]
    · rw [if_pos (by simp [h])]
      have hgt : (1 : ℝ) ≤ |(ρ : ℂ).im| := le_of_lt (not_le.mp h)
      have hmv : m ρ = |(ρ : ℂ).im| := by simp only [m]; exact max_eq_left hgt
      simp [ind, h, a, b, hmv]
  have hcs : ∑ ρ : ι, ind ρ * (a ρ * b ρ) ≤
      sqrt (∑ ρ : ι, ind ρ * (a ρ / m ρ)) *
        sqrt (∑ ρ : ι, ind ρ * (a ρ * m ρ * (b ρ) ^ 2)) := by
    have hstep : ∑ ρ : ι, ind ρ * (a ρ * b ρ) =
        ∑ ρ : ι, sqrt (ind ρ * (a ρ / m ρ)) *
          sqrt (ind ρ * (a ρ * m ρ * (b ρ) ^ 2)) := by
      refine Finset.sum_congr rfl ?_
      intro ρ _
      have hf0 : 0 ≤ ind ρ * (a ρ / m ρ) :=
        mul_nonneg (hind ρ) (div_nonneg (ha ρ) (le_of_lt (hm ρ)))
      have hprod : ind ρ * (a ρ / m ρ) * (ind ρ * (a ρ * m ρ * (b ρ) ^ 2)) =
          (ind ρ * (a ρ * b ρ)) ^ 2 := by
        have hmne : m ρ ≠ 0 := ne_of_gt (hm ρ)
        field_simp
        try ring
      rw [← Real.sqrt_mul (x := ind ρ * (a ρ / m ρ)) hf0]
      rw [hprod, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (mul_nonneg (hind ρ) (mul_nonneg (ha ρ) (hb ρ)))]
    rw [hstep]
    have h := Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
      (f := fun ρ : ι => ind ρ * (a ρ / m ρ))
      (g := fun ρ : ι => ind ρ * (a ρ * m ρ * (b ρ) ^ 2))
      (fun ρ => mul_nonneg (hind ρ) (div_nonneg (ha ρ) (le_of_lt (hm ρ))))
      (fun ρ => mul_nonneg (hind ρ) (mul_nonneg (mul_nonneg (ha ρ) (le_of_lt (hm ρ)))
        (sq_nonneg _)))
    simpa using h
  rw [hM, hI, hG]
  exact hcs


/-- LEAF. Page 43, display 4.42. Plancherel L2 identities yielding nTwo and nLog bounds. -/
theorem gaussian_moment_sum_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    sqrt (gaussianMomentSum χ δ T) ≤ sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T := by
  sorry

/-- LEAF. Page 40. Riemann-Stieltjes zero count error integrals. -/
theorem inv_im_sum_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    sqrt (invImSum χ T) * (sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T) ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  sorry

/-- Assembly. Exactly Decomp269b.middle_mass_bound. -/
theorem middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  have h1 := middle_mass_cauchy_schwarz q χ δ T hT
  have h2 := gaussian_moment_sum_bound q χ δ T hT
  have h3 := inv_im_sum_bound q χ hχ T hT hzeros
  have h_sqrt_nonneg : 0 ≤ sqrt (invImSum χ T) := sqrt_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h2 h_sqrt_nonneg
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
