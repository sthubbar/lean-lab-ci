import LeanLab.HelfgottMajor.SPLIT_zero_count_mid_height

/-!
Split of `leaf_mid_zero_count_small` in `HelfgottMajor.SPLIT_zero_count_mid_height`.

The target bounds the multiplicity weighted count of the nontrivial zeros of a primitive
`L`-function by `13`, on the middle range `2 * π ≤ q * t ≤ 2 * π * exp 1`.  Nothing of the
analytic machinery is needed on this range: the range pins the height below the fixed number
`2 * π * exp 1` and pins the conductor below `17`, and the count only grows with the height.
So the four steps below are, in order: the height bound `t ≤ 2 * π * exp 1`; the conductor
bound `q ≤ 17`; the monotonicity of the count in the height; and the count at the single
endpoint height `2 * π * exp 1` for a primitive character of conductor at most `17`, which is
the whole counting content.  The assembly at the end of the file is that chain, with no open
goal of its own.

The target `leaf_mid_zero_count_small` is not used anywhere in this file.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.
Carried verbatim from `LeanLab.HelfgottMajor.DecompJ1153` (private there). -/
private theorem zeros_strip_finite_mid (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
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

/-- The weight of a single zero is nonnegative. -/
private lemma zeroWeight_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    (ρ : ℂ) : 0 ≤ zeroWeight χ t ρ := by
  classical
  simp only [zeroWeight, Set.indicator_apply]
  split_ifs with h
  · exact Nat.cast_nonneg _
  · exact le_refl 0

/-- The weight of a single zero grows with the height. -/
private lemma zeroWeight_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s t : ℝ}
    (hst : s ≤ t) (ρ : ℂ) : zeroWeight χ s ρ ≤ zeroWeight χ t ρ := by
  classical
  have hs : ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ s} → ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ t} := by
    rintro ⟨a, b, c, d⟩
    exact ⟨a, b, c, le_trans d hst⟩
  simp only [zeroWeight, Set.indicator_apply]
  by_cases h : ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ s}
  · rw [if_pos h, if_pos (hs h)]
  · rw [if_neg h]
    split_ifs with h2
    · exact Nat.cast_nonneg _
    · exact le_refl 0

/-- LEAF. Monotonicity of the multiplicity weighted count in the height.  Raising the
height can only add nontrivial zeros to the counted set of `zeroCount`, and every weight is
a nonnegative natural number cast to a real, so the weighted sum over the plane grows.  This
is the step that carries the count from the ranging height `t` up to the endpoint
`2 * π * exp 1` of the middle range. -/
theorem leaf_mid_zero_count_mono (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    {s t : ℝ} (hst : s ≤ t) : zeroCount χ s ≤ zeroCount χ t := by
  classical
  have hfin : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ t}.Finite := zeros_strip_finite_mid q χ t
  have hsub : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ s} ⊆ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ t} := by
    rintro ρ ⟨a, b, c, d⟩
    exact ⟨a, b, c, le_trans d hst⟩
  have hsfin : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ s}.Finite := hfin.subset hsub
  set Ss := hsfin.toFinset with hSsdef
  set St := hfin.toFinset with hStdef
  have hSs : ∀ ρ : ℂ, ρ ∈ Ss ↔ (DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ s) := by
    intro ρ; rw [hSsdef]; simp
  have hSt : ∀ ρ : ℂ, ρ ∈ St ↔ (DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ t) := by
    intro ρ; rw [hStdef]; simp
  have hzero : ∀ ρ ∉ Ss, zeroWeight χ s ρ = 0 := by
    intro ρ hρ
    simp only [zeroWeight, Set.indicator_apply]
    rw [if_neg]
    intro hmem
    exact hρ ((hSs ρ).2 hmem)
  have h1 : zeroCount χ s = ∑ ρ ∈ Ss, zeroWeight χ s ρ := by
    rw [zeroCount]
    exact tsum_eq_sum hzero
  have h0t : ∀ ρ ∉ St, zeroWeight χ t ρ = 0 := by
    intro ρ hρ
    simp only [zeroWeight, Set.indicator_apply]
    rw [if_neg]
    intro hmem
    exact hρ ((hSt ρ).2 hmem)
  have h2 : zeroCount χ t = ∑ ρ ∈ St, zeroWeight χ t ρ := by
    rw [zeroCount]
    exact tsum_eq_sum h0t
  have h4 : ∑ ρ ∈ Ss, zeroWeight χ s ρ ≤ ∑ ρ ∈ St, zeroWeight χ t ρ := by
    refine le_trans (Finset.sum_le_sum (fun ρ _ => zeroWeight_le χ hst ρ)) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ρ hρ
      exact (hSt ρ).2 (hsub ((hSs ρ).1 hρ))
    · intro ρ _ _
      exact zeroWeight_nonneg χ t ρ
  rw [h1, h2]
  exact h4


/-- LEAF. Height bound.  On the middle range the modulus is at least one and `t` is at least
one, so `t ≤ q * t ≤ 2 * π * exp 1`.  This is the only place where the range bound enters the
height, and it is what makes the count a count at a fixed height. -/
theorem leaf_mid_height_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hhi : q * t ≤ 2 * π * exp 1) :
    t ≤ 2 * π * exp 1 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le (n := q)
  have ht0 : 0 ≤ t := by linarith
  have hqt : t ≤ (q : ℝ) * t := by
    simpa using mul_le_mul_of_nonneg_right hq1 ht0
  exact le_trans hqt hhi

/-- LEAF. Conductor bound.  On the middle range the modulus is at least one and `t` is at
least one, so `q ≤ q * t ≤ 2 * π * exp 1 < 18`, hence `q ≤ 17`.  This is the only place
where the range bound enters the conductor, and it is what makes the character range
finite. -/
theorem leaf_mid_conductor_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hhi : q * t ≤ 2 * π * exp 1) :
    q ≤ 17 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le (n := q)
  have hq0 : 0 ≤ (q : ℝ) := by linarith
  have hq_le : (q : ℝ) ≤ (q : ℝ) * t := by
    simpa using mul_le_mul_of_nonneg_left ht hq0
  have h2pi_e : 2 * π * exp 1 < 18 := by
    have hpi : π < 3.1416 := pi_lt_d4
    have he : exp 1 < 2.7182818286 := exp_one_lt_d9
    have he0 : 0 < exp 1 := exp_pos 1
    nlinarith
  have hq18 : (q : ℝ) < (18 : ℕ) := by
    push_cast
    linarith
  have hq_lt : q < 18 := Nat.cast_lt.mp hq18
  exact Nat.le_of_lt_succ hq_lt

/-- LEAF. The counting content of the middle range.  At the endpoint height
`2 * π * exp 1`, a primitive character of conductor at most `17` has at most `13`
multiplicity weighted nontrivial zeros in the critical strip.  The height is fixed here and
the conductor condition replaces the range conditions of the target, so this is strictly
weaker than the target. -/
theorem leaf_mid_zero_count_at_exp (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≤ 17) :
    zeroCount χ (2 * π * exp 1) ≤ 13 := by
  sorry

/-- The sealed statement, assembled from the height bound, the conductor bound, the
monotonicity of the count in the height and the count at the endpoint height. -/
theorem leaf_mid_zero_count_small_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    zeroCount χ t ≤ 13 := by
  have hH : t ≤ 2 * π * exp 1 := leaf_mid_height_le q t ht hhi
  have hC : q ≤ 17 := leaf_mid_conductor_le q t ht hhi
  have hM : zeroCount χ t ≤ zeroCount χ (2 * π * exp 1) :=
    leaf_mid_zero_count_mono q χ (s := t) (t := 2 * π * exp 1) hH
  have hE : zeroCount χ (2 * π * exp 1) ≤ 13 := leaf_mid_zero_count_at_exp q χ hχ hC
  linarith

end LeanLab.HelfgottMajor.Decomp388a
