import LeanLab.HelfgottMajor.SPLIT_leaf_band_zero_count_at_top_small_level
import LeanLab.PNTPort.DirichletZF.U1482Jensen

/-!
A conditional Lean refutation of the leaf `leaf_band_zero_count_at_top_level_one` of
`SPLIT_leaf_band_zero_count_at_top`.

That leaf asks, at conductor one, for at most `13` multiplicity weighted nontrivial zeros of
`ζ` up to the height `2 * π * exp 1 * exp 1 = 46.4268…`.  The head note of the split file and
the LOG lines of burst-20261122, sessions S94 and S98, report it FALSE numerically: `ζ` has
eight zeros with ordinate in `(0, 46.43)`, `14.1347, 21.0220, 25.0109, 30.4249, 32.9351,
37.5862, 40.9187, 43.3271`, and their eight conjugates, so the count is at least `16`.

This file turns that report into a kernel checked implication.  It assumes two cited numerical
facts as hypotheses and derives the negation of the leaf with no open goal:

* `hRH`: every nontrivial zero of `ζ` with `|Im ρ| ≤ 2 * π * exp 1 * exp 1` lies on the
  critical line.  This is the verification of the Riemann hypothesis to height `3 * 10 ^ 12`,
  Platt and Trudgian, Bull. LMS 53, 2021, far beyond `46.43`; it is used only to know that the
  count is a finite sum, which is what makes the `tsum` in `zeroCount` meaningful.
* `hzero`: eight distinct positive ordinates `γ k ≤ 46` with `ζ (1/2 + i γ k) = 0`.  These are
  the first eight zeros of `ζ`, in the tables of Odlyzko and of the LMFDB, each isolated by a
  sign change of the Hardy `Z` function.

The theorem is CONDITIONAL ON those two inputs.  It is not a numerical claim of its own: what is
checked by the kernel is that the leaf, the conjugation symmetry of `ζ` and the two inputs are
jointly inconsistent.  The leaf itself stays open in its file; no statement is changed.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp388a.RefuteLevelOne
open Real DecompJ1153

/-- A zero of `ζ` away from the pole has multiplicity at least one.  Same argument as the
private lemma `one_le_analyticOrderNatAt_zeta` of `SPLIT_gaussian_count_le_integral`, through the
entire function `(s - 1) ζ s` of `U1482Jensen`. -/
theorem one_le_order_zeta {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hne : ρ ≠ 1) :
    1 ≤ analyticOrderNatAt riemannZeta ρ := by
  have hf : AnalyticOnNhd ℂ LeanLab.PNTPort.DirichletZF.U1482.gZ Set.univ := fun z _ =>
    LeanLab.PNTPort.DirichletZF.U1482.gZ_analyticAt z
  have hana : AnalyticAt ℂ LeanLab.PNTPort.DirichletZF.U1482.gZ ρ := hf ρ (Set.mem_univ ρ)
  have hne2 : LeanLab.PNTPort.DirichletZF.U1482.gZ 2 ≠ 0 := by
    rw [LeanLab.PNTPort.DirichletZF.U1482.gZ_of_ne (by norm_num)]
    have h := riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num)
    have hone : ((2 : ℂ) - 1) ≠ 0 := by norm_num
    exact mul_ne_zero hone h
  have htop : analyticOrderAt LeanLab.PNTPort.DirichletZF.U1482.gZ ρ ≠ ⊤ := by
    intro h
    have hzero : LeanLab.PNTPort.DirichletZF.U1482.gZ =ᶠ[nhds ρ] 0 :=
      analyticOrderAt_eq_top.mp h
    have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ ρ) hzero (Set.mem_univ (2 : ℂ))
    exact hne2 hall
  have hg0 : LeanLab.PNTPort.DirichletZF.U1482.gZ ρ = 0 := by
    rw [LeanLab.PNTPort.DirichletZF.U1482.gZ_of_ne hne, hρ, mul_zero]
  have h0 : analyticOrderAt LeanLab.PNTPort.DirichletZF.U1482.gZ ρ ≠ 0 :=
    hana.analyticOrderAt_ne_zero.mpr hg0
  rw [← LeanLab.PNTPort.DirichletZF.U1482.ord_gZ hne, Nat.one_le_iff_ne_zero]
  intro hc
  apply h0
  rw [← Nat.cast_analyticOrderNatAt htop, hc]
  simp

/-- The top of the band at conductor one is above `46`: `2 π e² > 2 · 3.14 · 7.38 > 46`. -/
theorem top_height_gt_46 : (46 : ℝ) < 2 * π * exp 1 * exp 1 / ((1 : ℕ) : ℝ) := by
  have he := (top_exp_sq_bounds).1
  have hpi := Real.pi_gt_d2
  rw [Nat.cast_one, div_one, mul_assoc]
  nlinarith

/-- Conditional refutation of `leaf_band_zero_count_at_top_level_one`.  CONDITIONAL ON the
critical line verification `hRH` up to the band top and on eight distinct zeros of `ζ` on the
critical line with ordinates in `(0, 46]`, both cited in the module note.  Under these inputs the
multiplicity weighted count at conductor one is at least `16`, and the leaf's bound `13` fails. -/
theorem not_leaf_band_zero_count_at_top_level_one
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 2 * π * exp 1 * exp 1 → s.re = 1 / 2)
    (γ : Fin 8 → ℝ) (hγinj : Function.Injective γ) (hγpos : ∀ k, 0 < γ k)
    (hγle : ∀ k, γ k ≤ 46)
    (hzero : ∀ k, riemannZeta ((1 / 2 : ℂ) + (γ k : ℂ) * Complex.I) = 0) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → q = 1 →
      zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13) := by
  intro hleaf
  set χ : DirichletCharacter ℂ 1 := 1 with hχdef
  set H : ℝ := 2 * π * exp 1 * exp 1 / ((1 : ℕ) : ℝ) with hH
  have hle : zeroCount χ H ≤ 13 := hleaf 1 χ (DirichletCharacter.isPrimitive_one_level_one) rfl
  have hL : DirichletCharacter.LFunction χ = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  have hH' : H = 2 * π * exp 1 * exp 1 := by rw [hH, Nat.cast_one, div_one]
  -- finiteness of the support, hence summability
  have hfin : (Function.support (zeroWeight χ H)).Finite := by
    apply zero_weight_finite_support χ H
    intro s hs h0 h1 hT
    rw [hL] at hs
    exact hRH s hs h0 h1 (hH' ▸ hT)
  have hsum : Summable (zeroWeight χ H) :=
    summable_of_ne_finset_zero (s := hfin.toFinset) (fun b hb => by
      simpa [Set.Finite.mem_toFinset, Function.mem_support] using hb)
  -- the sixteen zeros
  let f : Fin 8 × Bool → ℂ := fun p =>
    (1 / 2 : ℂ) + ((if p.2 then γ p.1 else -γ p.1 : ℝ) : ℂ) * Complex.I
  have him : ∀ p, (f p).im = (if p.2 then γ p.1 else -γ p.1) := by
    intro p; simp [f]
  have hre : ∀ p, (f p).re = 1 / 2 := by
    intro p; simp [f]
  have hfinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hab
    have h := congrArg Complex.im hab
    rw [him, him] at h
    have ha := hγpos a
    have hc := hγpos c
    cases b <;> cases d <;> simp at h
    · exact Prod.ext (hγinj h) rfl
    · linarith
    · linarith
    · exact Prod.ext (hγinj h) rfl
  have hfz : ∀ p, riemannZeta (f p) = 0 := by
    rintro ⟨k, b⟩
    cases b
    · have hc : f (k, false) = (starRingEnd ℂ) ((1 / 2 : ℂ) + (γ k : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp [f]
      rw [hc, riemannZeta_conj, hzero k, map_zero]
    · have hc : f (k, true) = (1 / 2 : ℂ) + (γ k : ℂ) * Complex.I := by
        simp [f]
      rw [hc, hzero k]
  have hw : ∀ p, 1 ≤ zeroWeight χ H (f p) := by
    intro p
    have hne : f p ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hre] at this
      norm_num at this
    have habs : |(f p).im| ≤ H := by
      rw [him]
      have h46 := top_height_gt_46
      have hp := hγpos p.1
      have hl := hγle p.1
      split_ifs
      · rw [abs_of_pos hp]; linarith
      · rw [abs_neg, abs_of_pos hp]; linarith
    have hmem : f p ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ H} := by
      refine ⟨?_, ?_, ?_, habs⟩
      · rw [hL]; exact hfz p
      · rw [hre]; norm_num
      · rw [hre]; norm_num
    rw [zeroWeight, Set.indicator_of_mem hmem, hL]
    exact_mod_cast one_le_order_zeta (hfz p) hne
  have hnonneg : ∀ ρ, 0 ≤ zeroWeight χ H ρ := by
    intro ρ
    unfold zeroWeight
    exact Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg _) ρ
  have h16 : (16 : ℝ) ≤ zeroCount χ H := by
    have hsle := hsum.sum_le_tsum (Finset.univ.map ⟨f, hfinj⟩) (fun ρ _ => hnonneg ρ)
    rw [Finset.sum_map] at hsle
    have hlow : ∑ p : Fin 8 × Bool, (1 : ℝ) ≤
        ∑ p : Fin 8 × Bool, zeroWeight χ H (f p) :=
      Finset.sum_le_sum (fun p _ => hw p)
    have hcard : ∑ p : Fin 8 × Bool, (1 : ℝ) = 16 := by
      simp [Finset.sum_const, Finset.card_univ]
    unfold zeroCount
    simp only [Function.Embedding.coeFn_mk] at hsle
    linarith
  linarith

end LeanLab.HelfgottMajor.Decomp388a.RefuteLevelOne

#print axioms LeanLab.HelfgottMajor.Decomp388a.RefuteLevelOne.not_leaf_band_zero_count_at_top_level_one
