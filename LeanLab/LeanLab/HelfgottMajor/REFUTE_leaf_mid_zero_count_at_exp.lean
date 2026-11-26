import LeanLab.HelfgottMajor.SPLIT_leaf_mid_zero_count_small

/-!
A conditional Lean refutation of the leaf `leaf_mid_zero_count_at_exp` of
`SPLIT_leaf_mid_zero_count_small`.

That leaf asks that every primitive character of conductor at most `17` have at most `13`
multiplicity weighted nontrivial zeros up to the height `2 * π * exp 1 = 17.079…`.  Burst
burst-20261122, sessions S95 and S98, reported it FALSE numerically: every primitive character
mod `17` has `14` to `16` zeros with `|γ| ≤ 2 * π * exp 1`, the quadratic one has `16` on the
critical line, see `notes/burst-20261122/HelfgottMajor-leaf_mid_zero_count_at_exp-FALSE.md` and
the script `leaf_mid_zero_count_at_exp_check.py` there.

This file turns that report into a kernel checked implication.  For a fixed nonprincipal
primitive character of conductor at most `17` it assumes one cited numerical input, `hz`:
fourteen distinct zeros of its `L`-function in the critical strip with `|Im ρ| ≤ 2 * π * exp 1`.
For the quadratic character mod `17` these are among the sixteen critical line zeros found by
sign changes of the Hardy `Z` function in the burst-20261122 script, and they agree with the
LMFDB data of the `L`-function of that character.  From that input alone it derives the negation
of the leaf.  The finiteness of the zero set, needed for the count to be a finite sum, is proved
here and is not an input.

The theorem is CONDITIONAL ON that one input.  The leaf itself stays open in its file; no
statement is changed.  AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp388a.RefuteMidAtExp
open Real DecompJ1153

/-- The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.
Carried verbatim from `SPLIT_leaf_mid_zero_count_small`, private there. -/
theorem zeros_strip_finite_mid' (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
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


/-- A zero of a nonprincipal `L`-function has multiplicity at least one.  Same argument as the
private lemma `one_le_analyticOrderNatAt_LFunction` of `SPLIT_gaussian_count_le_integral`:
`L χ` is entire and not identically zero. -/
theorem one_le_order_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
  set f := DirichletCharacter.LFunction χ with hfdef
  have hf : AnalyticOnNhd ℂ f Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hana : AnalyticAt ℂ f ρ := hf ρ (Set.mem_univ ρ)
  have hne : f 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  have htop : analyticOrderAt f ρ ≠ ⊤ := by
    intro h
    have hzero : f =ᶠ[nhds ρ] 0 := analyticOrderAt_eq_top.mp h
    have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ ρ) hzero (Set.mem_univ (2 : ℂ))
    exact hne hall
  have h0 : analyticOrderAt f ρ ≠ 0 := hana.analyticOrderAt_ne_zero.mpr hρ
  rw [Nat.one_le_iff_ne_zero]
  intro hc
  apply h0
  rw [← Nat.cast_analyticOrderNatAt htop, hc]
  simp

/-- Conditional refutation of `leaf_mid_zero_count_at_exp`.  CONDITIONAL ON `hz`, fourteen
distinct zeros in the critical strip up to height `2 * π * exp 1` of the `L`-function of one
nonprincipal primitive character of conductor at most `17`, cited in the module note.  Under
that input the multiplicity weighted count at that height is at least `14`, and the leaf's
bound `13` fails. -/
theorem not_leaf_mid_zero_count_at_exp (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≤ 17) (hχ1 : χ ≠ 1)
    (z : Fin 14 → ℂ) (hzinj : Function.Injective z)
    (hz : ∀ k, DirichletCharacter.LFunction χ (z k) = 0 ∧ 0 < (z k).re ∧ (z k).re < 1 ∧
      |(z k).im| ≤ 2 * π * exp 1) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → q ≤ 17 →
      zeroCount χ (2 * π * exp 1) ≤ 13) := by
  intro hleaf
  set H : ℝ := 2 * π * exp 1 with hH
  have hle : zeroCount χ H ≤ 13 := hleaf q χ hχ hq
  have hfin : (Function.support (zeroWeight χ H)).Finite := by
    apply (zeros_strip_finite_mid' q χ H).subset
    intro ρ hρ
    by_contra hh
    exact hρ (by
      simp only [zeroWeight]
      exact Set.indicator_of_notMem hh _)
  have hsum : Summable (zeroWeight χ H) :=
    summable_of_ne_finset_zero (s := hfin.toFinset) (fun b hb => by
      simpa [Set.Finite.mem_toFinset, Function.mem_support] using hb)
  have hnonneg : ∀ ρ, 0 ≤ zeroWeight χ H ρ := by
    intro ρ
    unfold zeroWeight
    exact Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg _) ρ
  have hw : ∀ k, 1 ≤ zeroWeight χ H (z k) := by
    intro k
    have hmem : z k ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ H} := hz k
    rw [zeroWeight, Set.indicator_of_mem hmem]
    exact_mod_cast one_le_order_LFunction χ hχ1 (hz k).1
  have h14 : (14 : ℝ) ≤ zeroCount χ H := by
    have hsle := hsum.sum_le_tsum (Finset.univ.map ⟨z, hzinj⟩) (fun ρ _ => hnonneg ρ)
    rw [Finset.sum_map] at hsle
    have hlow : ∑ k : Fin 14, (1 : ℝ) ≤ ∑ k : Fin 14, zeroWeight χ H (z k) :=
      Finset.sum_le_sum (fun k _ => hw k)
    have hcard : ∑ k : Fin 14, (1 : ℝ) = 14 := by
      simp [Finset.sum_const, Finset.card_univ]
    unfold zeroCount
    simp only [Function.Embedding.coeFn_mk] at hsle
    linarith
  linarith

end LeanLab.HelfgottMajor.Decomp388a.RefuteMidAtExp

#print axioms LeanLab.HelfgottMajor.Decomp388a.RefuteMidAtExp.not_leaf_mid_zero_count_at_exp
