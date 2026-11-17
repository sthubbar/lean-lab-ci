import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le

/-!
Split of `positive_mass_window_one_high_half_le` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le` into five leaves.

The statement being split bounds the multiplicity weighted sum of the Gaussian Mellin norms
attached to the positive zeros of a Dirichlet `L`-function in the strip `0 < re < 1` and below
height `T`, restricted to the ordinate band above five quarters and at most three halves, by a
quarter of the critical line norm integral against the mean log weight on `[1, T]`.

The split separates four things the bound needs. First, the band family has to converge at all:
the statement is a sum over every zero in the strip below height `T` and carries no hypothesis on
the zeros, so nothing in the closure makes that family summable, and a family that does not
converge has no additivity to offer over a cut of the band. Second, the band is cut at seven
fifths into two sub-bands of equal length, each charged half the budget; a zero sitting exactly on
the cut belongs to the lower sub-band and is counted once. Third, each sub-band is estimated
against the *positive part* of the mean log weight, one eighth of the integral each, which is what
keeps the two estimates meaningful where the log weight changes sign. Fourth, the transfer from
that positive part back to the signed weight, which is the only place where the sign of
`log (q * t / (2 * pi))` on `[1, T]` is used.

That transfer is where this cut of the statement is loose: the positive part dominates the signed
weight pointwise, so the inequality of the fifth leaf is a claim about the two integrals being
equal in the direction that the argument needs, and it fails as soon as the log weight is negative
somewhere on `[1, T]`, which for `q <= 6` happens for every height. The first four leaves are
sound; the fifth is the defect of the statement being split, isolated on its own.

The assembly is exactly three ingredients: the identity of sums over the two sub-bands, which is
where the convergence leaf is spent, the addition of the two sub-band estimates, and the transfer
leaf. It has no sorry of its own.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.

Multiplier trick: `s ↦ (s - 1) * L χ s` is entire (for the trivial character the
pole-removed `LFunctionTrivChar₁` is used instead), it vanishes at every zero of `L χ`
inside the strip, and it is not identically zero. Hence its zero set is discrete, and a
closed bounded box meets it finitely. This is the input the summability leaf spends. -/
private theorem zeros_strip_finite_431a (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
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

/-- LEAF 1 of 5, the convergence of the band family. The nonnegative family of the Gaussian
Mellin norms at the zeros in the strip below height `T` is summable. Below a fixed height the
ordinates lie in a compact rectangle and the zeros there are isolated, so only finitely many of
them carry weight; this is the input the sub-band identity below needs, and it is stated on its
own because a sum of the norms over a family that does not converge has no additivity to offer
over a cut of the ordinate range. -/
theorem high_half_norm_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  classical
  haveI : Finite {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} :=
    Set.Finite.to_subtype (zeros_strip_finite_431a q χ T)
  exact Summable.of_finite


/-- LEAF 2 of 5, the sub-band identity. Given the convergence of the band family, the sum over the
ordinates above five quarters and at most three halves is the sum over the ordinates above five
quarters and at most seven fifths, plus the sum over the ordinates above seven fifths and at most
three halves. As a statement this is the additivity of the zero sum over a disjoint cut of the
band, and it is the only place where the convergence leaf is spent. -/
theorem high_half_window_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 7 / 5}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 5 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) := by
  have hkey : ∀ (x v : ℝ), (if (5 / 4 : ℝ) < x ∧ x ≤ 3 / 2 then v else 0) =
      (if (5 / 4 : ℝ) < x ∧ x ≤ 7 / 5 then v else 0) +
        (if (7 / 5 : ℝ) < x ∧ x ≤ 3 / 2 then v else 0) := by
    intro x v
    by_cases h1 : (5 / 4 : ℝ) < x
    · by_cases h2 : x ≤ 3 / 2
      · by_cases h3 : x ≤ 7 / 5
        · rw [if_pos ⟨h1, h2⟩, if_pos ⟨h1, h3⟩,
            if_neg (by intro h; linarith [h.1, h3])]
          ring
        · rw [if_pos ⟨h1, h2⟩, if_neg (by intro h; linarith [h.2, h3]),
            if_pos ⟨lt_of_not_ge h3, h2⟩]
          ring
      · rw [if_neg (by intro h; linarith [h.2, h2]),
            if_neg (by intro h; linarith [h.2, h2]),
            if_neg (by intro h; linarith [h.2, h2])]
        ring
    · rw [if_neg (by intro h; linarith [h.1, h1]),
          if_neg (by intro h; linarith [h.1, h1]),
          if_neg (by intro h; linarith [h.1, h1])]
      ring
  have hpt : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
      Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ =
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 7 / 5}
            (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ +
          Set.indicator {ρ | 7 / 5 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
            (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ := by
    intro ρ
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      hkey ρ.val.im ‖mellinMassTerm χ δ ρ.val‖
  refine (tsum_congr hpt).trans ?_
  exact Summable.tsum_add (hs.indicator _) (hs.indicator _)

/-- LEAF 3 of 5, the lower sub-band against the nonnegative weight. The multiplicity weighted sum
of the Gaussian Mellin norms over the zeros whose ordinate lies above five quarters and at most
seven fifths is at most one eighth of the mean weight integral, where the weight is the positive
part of the log weight. This sub-band carries the smaller ordinates of the band and pays the half
of the budget that has to absorb them. -/
theorem high_half_low_part_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 7 / 5}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          max (log ((q : ℝ) * t / (2 * π))) 0)) := by
  sorry

/-- LEAF 4 of 5, the upper sub-band against the nonnegative weight. The multiplicity weighted sum
of the Gaussian Mellin norms over the zeros whose ordinate lies above seven fifths and at most
three halves is at most one eighth of the mean weight integral against the positive part of the log
weight. This sub-band has the same length as the lower one, carries no endpoint term, and is
charged the same eighth of the budget. -/
theorem high_half_high_part_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 5 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          max (log ((q : ℝ) * t / (2 * π))) 0)) := by
  sorry

/-- LEAF 5 of 5, the transfer from the positive part of the log weight back to the signed log
weight. A quarter of the mean weight integral against the positive part is at most the same
quarter against the signed log weight. This is the step that replaces the weight by itself, and it
is where the sign of `log (q * t / (2 * pi))` on the height interval is used: the positive part
dominates the signed weight, so the inequality is an equality claim on the integrals and holds only
where the log weight has no negative part on `[1, T]`. -/
theorem high_half_weight_pos_part_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          max (log ((q : ℝ) * t / (2 * π))) 0)) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  sorry

/-- The two sub-bands add up to the bound of `positive_mass_window_one_high_half_le`. The band
`(5 / 4, 3 / 2]` cuts at seven fifths into two disjoint sub-bands, the convergence leaf makes that
cut an identity of sums, the two shares of one eighth each add up to one quarter, and the transfer
leaf replaces the positive part of the weight by the signed log weight. -/
theorem positive_mass_window_one_high_half_le_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π)))) := by
  have hs := high_half_norm_summable q χ δ T hT
  have hsplit := high_half_window_split q χ δ T hT hs
  have hcalc :
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) +
        (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) =
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) := by
    ring
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)
      = ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 5 / 4 < ρ.val.im ∧ ρ.val.im ≤ 7 / 5}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) +
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 5 < ρ.val.im ∧ ρ.val.im ≤ 3 / 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ)) := hsplit
    _ ≤ (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) +
        (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) :=
      add_le_add (high_half_low_part_le q χ δ T hT) (high_half_high_part_le q χ δ T hT)
    _ = (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            max (log ((q : ℝ) * t / (2 * π))) 0)) := hcalc
    _ ≤ (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π)))) := high_half_weight_pos_part_le q χ δ T hT

end LeanLab.HelfgottMajor.Decomp431a
