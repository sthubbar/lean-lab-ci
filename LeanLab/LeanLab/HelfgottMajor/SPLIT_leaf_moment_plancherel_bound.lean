import LeanLab.HelfgottMajor.SPLIT_gaussian_moment_sum_bound

/-!
Split of the open Gaussian moment bound `leaf_moment_plancherel_bound` of this folder.

The target bounds the zero sum `gaussianMomentSum χ δ T`, which carries the weight
`multiplicity * |im ρ| * ‖gaussianMellin δ ρ‖ ^ 2` over the zeros of `L χ` in the strip
`0 < re < 1` with `1 < |im ρ| ≤ T`, by `(Sec45.nTwo + Sec45.nLog) * T`.

The split has three steps.  Every zero in the index set has `|im ρ| ≤ T`, so the height
factor can be pulled out of the sum and replaced by `T`, at the price of dropping the
weight `|im ρ|`.  The threshold `1 < |im ρ|` is a nonnegative cutoff, so dropping it only
increases the mass.  The remaining mass, the sum of multiplicities times squared Mellin
norms, is the discrete Plancherel quantity that the two closed-form `L2` energies
`Sec45.nTwo` and `Sec45.nLog` of the Gaussian profile dominate.  Multiplying the resulting
bound by the nonnegative height `T` gives the target.  Each step is a separate leaf ending
in `sorry`; the assembly `leaf_moment_plancherel_bound_split` below uses only those leaves.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.

Same multiplier trick as `zeros_strip_finite` of `DecompJ1153`, which is `private` and so not
available here: `s ↦ (s - 1) * L χ s` (or the pole-removed `LFunctionTrivChar₁` in the
trivial case) is entire, vanishes at every strip zero of `L χ`, and is not identically zero;
its zero set is discrete, and a closed bounded box meets it finitely. -/
private theorem zeros_strip_finite_mpb (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
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

/-- LEAF. Height pull-out.  Every zero in the index set satisfies `|im ρ| ≤ T`, the
multiplicity is a nonnegative natural number and the squared Mellin norm is nonnegative, so
the weighted zero sum is at most `T` times the zero sum in which the weight `|im ρ|` is
replaced by `1`.  No information about the Mellin norms is used, only the height window and
nonnegativity; the statement is empty (both sides `0`) when the window holds no zero. -/
theorem leaf_moment_height_pullout (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    gaussianMomentSum χ δ T ≤
      T * (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ T},
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
  classical
  set ι := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
    with hι
  haveI : Fintype ι := hι.symm ▸ (zeros_strip_finite_mpb q χ T).fintype
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  simp only [gaussianMomentSum, tsum_fintype]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro ρ _
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases h : |(ρ : ℂ).im| ≤ 1
  · rw [if_neg (by simp [h]), if_neg (by simp [h])]
    simp
  · rw [if_pos (by simp [h]), if_pos (by simp [h])]
    have him : |(ρ : ℂ).im| ≤ T := ρ.property.2.2.2
    have ha : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) :=
      Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2 := sq_nonneg _
    have hAB : (0 : ℝ) ≤
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) *
          ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2 := mul_nonneg ha hb
    have hmul := mul_le_mul_of_nonneg_right him hAB
    calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) * |(ρ : ℂ).im| *
          ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2
        = |(ρ : ℂ).im| * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) *
            ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2) := by ring
      _ ≤ T * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) (ρ : ℂ) : ℝ) *
            ‖gaussianMellin δ (ρ : ℂ)‖ ^ 2) := hmul

/-- LEAF. Cutoff removal.  The cutoff `1 < |im ρ|` contributes the factor `1` on the zeros it
keeps and `0` on the zeros with `|im ρ| ≤ 1`, whose contribution is nonnegative; so the
indicator can be dropped and the mass can only grow.  This is a termwise comparison of two
sums over the same index set, with no estimate of the Mellin norms. -/
theorem leaf_moment_mass_indicator_le_full (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2 := by
  classical
  set ι := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
    with hι
  haveI : Fintype ι := hι.symm ▸ (zeros_strip_finite_mpb q χ T).fintype
  simp only [tsum_fintype]
  refine Finset.sum_le_sum ?_
  intro ρ _
  rw [Set.indicator_apply]
  by_cases h : |(ρ : ℂ).im| ≤ 1
  · rw [if_neg (by simp [h])]
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  · rw [if_pos (by simp [h])]

/-- LEAF. Plancherel mass bound.  The sum over the strip zeros of the multiplicity times the
squared Mellin norm of the Gaussian profile at that zero is at most the sum of the two
squared `L2` energies of the profile, `Sec45.nTwo` and the log-weighted `Sec45.nLog`.  This
is the discrete sampling estimate that turns the two closed forms of the Gaussian energies
into a bound on the zero sum; it is uniform in the height window `|im ρ| ≤ T` and holds
trivially when the window is empty. -/
theorem leaf_moment_full_mass_plancherel (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2) ≤
    Sec45.nTwo + Sec45.nLog := by
  sorry

/-- Assembly of the split: pull the height `T` out of the zero sum, drop the unit cutoff and
use the Plancherel mass bound, then move the two energies past the height. -/
theorem leaf_moment_plancherel_bound_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    gaussianMomentSum χ δ T ≤ (Sec45.nTwo + Sec45.nLog) * T := by
  set M : ℝ :=
    ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ T},
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ with hM
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have h1 : gaussianMomentSum χ δ T ≤ T * M := by
    simpa only [hM] using leaf_moment_height_pullout q χ δ T hT
  have h2 : M ≤ Sec45.nTwo + Sec45.nLog := by
    rw [hM]
    exact le_trans (leaf_moment_mass_indicator_le_full q χ δ T)
      (leaf_moment_full_mass_plancherel q χ δ T)
  calc gaussianMomentSum χ δ T ≤ T * M := h1
    _ ≤ T * (Sec45.nTwo + Sec45.nLog) := mul_le_mul_of_nonneg_left h2 hT0
    _ = (Sec45.nTwo + Sec45.nLog) * T := mul_comm _ _

end LeanLab.HelfgottMajor.DecompJ1153
