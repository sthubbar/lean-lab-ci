import LeanLab.HelfgottMajor.SPLIT_leaf_moment_plancherel_bound

/-!
Split of the open target `leaf_moment_full_mass_plancherel` of
`SPLIT_leaf_moment_plancherel_bound.lean`.

The target bounds the discrete Plancherel mass

`∑ (multiplicity of ρ) * ‖gaussianMellin δ ρ‖ ^ 2`

over the zeros `ρ` of `L χ` in the strip `0 < re ρ < 1` with `|im ρ| ≤ T` by the two
closed forms `Sec45.nTwo` and `Sec45.nLog`, with no dependence on the conductor `q`.

The split cuts the index set at the fixed height `|im ρ| ≤ 1`.  The windows in play are
finite, so both sides of the cut are honest finite sums and the total mass is the sum of
the two band masses.  Each band is then bounded by one of the two energy constants: the
low band `|im ρ| ≤ 1` by `Sec45.nTwo`, and the high band `1 < |im ρ| ≤ T` by
`Sec45.nLog`.  Adding the two bounds gives the target.  Each step is a separate leaf
ending in `sorry`; the assembly `leaf_moment_full_mass_plancherel_split` below uses only
those leaves and no `sorry`.

Diagnostic value of the cut: the low band is the piece that the zero count of the strip
drives, since the zeros with `|im ρ| ≤ 1` number about `log q / π`; the high band is the
piece that the Mellin decay of the Gaussian profile drives.  The low leaf therefore
isolates the whole `q` dependence of the target.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.

Same multiplier trick as `zeros_strip_finite` of `DecompJ1153`, which is `private` and so not
available here: `s ↦ (s - 1) * L χ s` (or the pole-removed `LFunctionTrivChar₁` in the
trivial case) is entire, vanishes at every strip zero of `L χ`, and is not identically zero;
its zero set is discrete, and a closed bounded box meets it finitely.  The same proof sits
as the `private` theorem `zeros_strip_finite_mpb` of the imported
`SPLIT_leaf_moment_plancherel_bound`. -/
private theorem zeros_strip_finite_mpf (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
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

/-- LEAF. Finiteness of the zero window.  The zeros of `L χ` in the strip `0 < re < 1`
with `|im| ≤ T` are the intersection of the strip box with the zero set of `L χ`, which is
discrete after removing the possible pole at `s = 1`; a closed bounded box meets a discrete
set finitely.  This leaf only supplies the `Fintype` instance that turns the two band sums
into finite sums; it estimates nothing about the sizes of the summands. -/
theorem leaf_moment_window_finite (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite :=
  zeros_strip_finite_mpf q χ T

/-- LEAF. Low band mass.  The part of the zero mass carried by the zeros with
`|im ρ| ≤ 1` is at most the squared `L2` energy `Sec45.nTwo` of the Gaussian profile.  The
height cutoff at `1` fixes the band once and for all, so the band sum is a sum over the
finitely many zeros in a fixed box, each weighted by its multiplicity and its squared Mellin
norm.  It says nothing about the zeros above height `1`. -/
theorem leaf_moment_low_mass_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nTwo := by
  sorry

/-- LEAF. High band mass.  The part of the zero mass carried by the zeros with
`1 < |im ρ| ≤ T` is at most the log-weighted squared `L2` energy `Sec45.nLog` of the
Gaussian profile.  The band excludes the finitely many zeros of height at most `1`, so the
summands are controlled by the decay of the Mellin transform in the height, which is what
`Sec45.nLog` measures.  This leaf says nothing about the band `|im ρ| ≤ 1`. -/
theorem leaf_moment_high_mass_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    Sec45.nLog := by
  sorry

/-- Assembly of the split: the window is finite, so the zero mass is the sum of its low
band `|im ρ| ≤ 1` and its high band `1 < |im ρ| ≤ T`; bounding the two bands by
`Sec45.nTwo` and `Sec45.nLog` gives the target. -/
theorem leaf_moment_full_mass_plancherel_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2) ≤
    Sec45.nTwo + Sec45.nLog := by
  classical
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ T} := (leaf_moment_window_finite q χ T).fintype
  have hsplit :
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2)
        = (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
              ρ.re < 1 ∧ |ρ.im| ≤ T},
            Set.indicator {ρ | |ρ.val.im| ≤ 1}
              (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                ‖gaussianMellin δ ρ.val‖ ^ 2) ρ)
          + (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
                ρ.re < 1 ∧ |ρ.im| ≤ T},
              Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
                (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
                  ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ρ _
    by_cases h : |(ρ : ℂ).im| ≤ 1
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [hsplit]
  have hlow := leaf_moment_low_mass_le q χ δ T
  have hhigh := leaf_moment_high_mass_le q χ δ T
  linarith

end LeanLab.HelfgottMajor.DecompJ1153
