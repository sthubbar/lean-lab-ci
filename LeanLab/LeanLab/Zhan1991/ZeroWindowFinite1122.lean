import LeanLab.Zhan1991.SPLIT_theorem3_p2_1122

/-!
P0068 Zhan 1991, page 262, the count `N(α, T, H, q)` of Lemma 4 is a finite count. PROVED,
closing the LEAF `zeroWindow_finite` of SPLIT_theorem3_p2_1122 by a separate proof, without
editing that file. burst-20261122, session S80.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

open Filter Topology

/-- Every point `z` has a punctured neighbourhood free of zeros of `L(s, χ)`: at the pole of the
principal character by the residue, elsewhere by isolated zeros, since `L(s, χ)` is analytic on
the connected set `ℂ \ {1}` and `L(2, χ) ≠ 0`. PROVED. -/
theorem lfun_isolated (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) :
    ∀ᶠ w in 𝓝 z, w ≠ z → DirichletCharacter.LFunction χ w ≠ 0 := by
  set f := DirichletCharacter.LFunction χ
  refine eventually_nhdsWithin_iff.mp ?_
  by_cases hz : z = 1 ∧ χ = 1
  · obtain ⟨rfl, rfl⟩ := hz
    have hr := DirichletCharacter.LFunctionTrivChar_residue_one (N := q)
    have hne : ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp h
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (p : ℂ)⁻¹ = 1 := by linear_combination -h
      have : (p : ℂ) = 1 := by simpa using congrArg (·⁻¹) this
      have : (p : ℝ) = 1 := by exact_mod_cast this
      linarith
    filter_upwards [hr.eventually_ne hne] with w hw
    intro h0
    exact hw (mul_eq_zero.mpr (Or.inr h0))
  · have hdiff : DifferentiableOn ℂ f {1}ᶜ := fun w hw =>
      (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw)).differentiableWithinAt
    have hanU : AnalyticOnNhd ℂ f {1}ᶜ := hdiff.analyticOnNhd isOpen_compl_singleton
    have hanz : AnalyticAt ℂ f z := by
      by_cases h1 : z = 1
      · have hχ : χ ≠ 1 := fun h => hz ⟨h1, h⟩
        exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
      · exact hanU z h1
    rcases hanz.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
        (isConnected_compl_singleton_of_one_lt_rank
          (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
      -- pick a point near z different from 1 where f vanishes eventually
      have hz' : ∃ w : ℂ, w ≠ 1 ∧ f =ᶠ[𝓝 w] 0 := by
        by_cases h1 : z = 1
        · have hev : ∀ᶠ w in 𝓝 z, ∀ᶠ y in 𝓝 w, f y = 0 := h.eventually_nhds
          have hne : ∀ᶠ w in 𝓝[≠] z, w ≠ 1 := by
            subst h1; exact self_mem_nhdsWithin
          obtain ⟨w, hw1, hw2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and hne).exists
          exact ⟨w, hw2, hw1⟩
        · exact ⟨z, h1, h⟩
      obtain ⟨w, hw1, hw⟩ := hz'
      have hEq := hanU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc hw1 hw
      have h2 : f 2 = 0 := hEq (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
        (by norm_num) h2
    · exact h

/-- Page 262, Lemma 4: for `α ≥ 1/2` the zeros of `L(s, χ)` in the window are finitely many; they
lie in the compact box `[α, 1] × [T, T + H]`, and each point of it has a neighbourhood holding no
other zero. PROVED. -/
theorem zeroWindow_finite_proof (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (α T H : ℝ)
    (_hα : 1 / 2 ≤ α) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
      ρ.im ≤ T + H}.Finite := by
  set f := DirichletCharacter.LFunction χ
  set S := {ρ : ℂ | f ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H}
  set K := Complex.equivRealProdCLM.symm '' (Set.Icc α 1 ×ˢ Set.Icc T (T + H))
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hSK : S ⊆ K := by
    intro ρ hρ
    refine ⟨(ρ.re, ρ.im), ⟨⟨hρ.2.1, ?_⟩, hρ.2.2.1, hρ.2.2.2⟩, ?_⟩
    · by_contra hlt
      push Not at hlt
      have hne : ρ ≠ 1 := by
        intro h; rw [h] at hlt; simp at hlt
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne) hlt.le hρ.1
    · rfl
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover
    (fun z => {w | w ≠ z → f w ≠ 0}) (fun z _ => lfun_isolated q χ z)
  refine (t.finite_toSet).subset ?_
  intro ρ hρ
  obtain ⟨z, hzt, hz⟩ := Set.mem_iUnion₂.mp (hcover (hSK hρ))
  by_contra hnot
  have : ρ ≠ z := fun h => hnot (h ▸ hzt)
  exact hz this hρ.1

/-- Page 269, window enlargement: `N(α, T, H, q)` is monotone in `H`. PROVED. -/
theorem zeroCountZ_mono_H_proof (q : ℕ) [NeZero q] (α T H H' : ℝ) (hα : 1 / 2 ≤ α)
    (hH : H ≤ H') : zeroCountZ α T H q ≤ zeroCountZ α T H' q :=
  zeroCountZ_mono_H_of q α T H H' hH fun χ => zeroWindow_finite_proof q χ α T H' hα

end LeanLab.Zhan1991
