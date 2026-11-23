import LeanLab.task783.RealZeroPairs

/-!
# Real zero sum leaf forces every real zero in (0, 1) to be 1/2

AI wrote this Lean code (Claude, a Claude Code subagent); it is not human reviewed.

Binary Goldbach is OPEN.  Nothing here bears on it directly.

This file checks the HelfgottMajor leaf
`LeanLab.HelfgottMajor.Decomp388a.endpoint_real_zero_sum_le` and its twin
`LeanLab.task783.endpoint_real_zero_sum_le`.  Every zero of `L(s, χ)` in the open critical strip
has multiplicity at least one, `mult_pos`, because `L(s, χ)` is analytic on the connected set
`ℂ \ {1}` and does not vanish at `2`.  Combined with the pairing `β ↔ 1 - β` of
`RealZeroPairs.real_zero_one_sub`, the leaf forces every real zero in `(0, 1)` to equal `1 / 2`.
The leaf is only taken as a hypothesis here; it is not used.
-/

namespace LeanLab.task783.RealZeroSum

open Real Complex

variable {q : ℕ} [NeZero q]

/-- `L(s, χ)` is analytic on `ℂ \ {1}`, for every character `χ`. -/
private lemma analyticOnNhd_LFunction (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
  refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
  exact (DirichletCharacter.differentiableAt_LFunction _ _ (.inl hs)).differentiableWithinAt

/-- Every zero of `L(s, χ)` away from `s = 1` has finite order, for every character `χ`:
the order is finite at `2`, where `L(s, χ)` does not vanish, and `ℂ \ {1}` is connected. -/
theorem analyticOrderAt_ne_top (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _)
      |>.isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hρ' : ρ ∈ ({1}ᶜ : Set ℂ) := hρ
  refine (analyticOnNhd_LFunction χ).analyticOrderAt_ne_top_of_isPreconnected hpc h2 hρ' ?_
  have h0 : analyticOrderAt (DirichletCharacter.LFunction χ) 2 = 0 := by
    rw [analyticOrderAt_eq_zero]
    right
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
      (by norm_num)
  rw [h0]
  exact ENat.zero_ne_top

/-- Every zero of `L(s, χ)` in the open critical strip has multiplicity at least one, for every
Dirichlet character `χ`, primitive or not.  The point is that `analyticOrderNatAt` would be `0`
if the order were infinite, and `analyticOrderAt_ne_top` excludes that. -/
theorem mult_pos (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hz : DirichletCharacter.LFunction χ ρ = 0) (h1 : ρ.re < 1) :
    1 ≤ LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ := by
  have hρ : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hne := analyticOrderAt_ne_top χ hρ
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    analyticOnNhd_LFunction χ ρ hρ
  have hpos : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨han, hz⟩
  unfold LeanLab.HelfgottMajor.ZeroCount1623.mult
  rw [← Nat.cast_analyticOrderNatAt hne] at hpos
  have : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
    exact_mod_cast hpos
  omega

/-- The HelfgottMajor LEAF `endpoint_real_zero_sum_le`, taken here as the hypothesis `hsum`,
implies that every real zero of `L(s, χ)` in `(0, 1)` equals `1 / 2`: the zeros `β` and `1 - β`
both lie in the filtered finset with weight at least one each, so if they were distinct the sum
would be at least `2`.  So that leaf, for every primitive character of modulus at least `2 π`,
excludes real zeros off `1 / 2`, in particular Landau-Siegel zeros, which is an open problem. -/
theorem real_zero_eq_half_of_sum_le_one (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ))
    (hsum : (∑ ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ
        (2 * π / q)).toFinset.filter (fun ρ => ρ.im = 0),
        (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ)) ≤ 1)
    {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hz : DirichletCharacter.LFunction χ β = 0) :
    β = 1 / 2 := by
  have hT : 0 ≤ 2 * π / (q : ℝ) := by positivity
  have hz' := RealZeroPairs.real_zero_one_sub χ hχ h0 h1 hz
  set S := (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ
      (2 * π / q)).toFinset.filter (fun ρ => ρ.im = 0) with hS
  have m1 : (β : ℂ) ∈ S := by
    simp only [hS, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨hz, by simpa using h0, by simpa using h1, by simpa using hT⟩, by simp⟩
  have m2 : ((1 - β : ℝ) : ℂ) ∈ S := by
    simp only [hS, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨by push_cast; exact hz', by simp; linarith, by simp; linarith,
      by simpa using hT⟩, by simp⟩
  by_contra hne
  have hdist : (β : ℂ) ≠ ((1 - β : ℝ) : ℂ) := by
    intro h
    have : β = 1 - β := by exact_mod_cast h
    exact hne (by linarith)
  have hsub : ({(β : ℂ), ((1 - β : ℝ) : ℂ)} : Finset ℂ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact m1
    · exact m2
  have hnn : ∀ ρ ∈ S, ρ ∉ ({(β : ℂ), ((1 - β : ℝ) : ℂ)} : Finset ℂ) →
      0 ≤ (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ) := fun _ _ _ => by positivity
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  rw [Finset.sum_pair hdist] at hle
  have e1 : (1 : ℝ) ≤ (LeanLab.HelfgottMajor.ZeroCount1623.mult χ (β : ℂ) : ℝ) := by
    exact_mod_cast mult_pos χ hz (by simpa using h1)
  have e2 : (1 : ℝ) ≤
      (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ((1 - β : ℝ) : ℂ) : ℝ) := by
    have hz2 : DirichletCharacter.LFunction χ ((1 - β : ℝ) : ℂ) = 0 := by
      push_cast; exact hz'
    exact_mod_cast mult_pos χ hz2 (by simp; linarith)
  linarith

/-- The same leaf also forces a zero at `1 / 2` to be simple: its weight alone is at most the
whole sum, which is at most `1`. -/
theorem half_zero_simple_of_sum_le_one (χ : DirichletCharacter ℂ q)
    (hsum : (∑ ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ
        (2 * π / q)).toFinset.filter (fun ρ => ρ.im = 0),
        (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ)) ≤ 1)
    (hz : DirichletCharacter.LFunction χ (1 / 2) = 0) :
    LeanLab.HelfgottMajor.ZeroCount1623.mult χ (1 / 2) ≤ 1 := by
  have hT : 0 ≤ 2 * π / (q : ℝ) := by positivity
  have m : (1 / 2 : ℂ) ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ
      (2 * π / q)).toFinset.filter (fun ρ => ρ.im = 0) := by
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨hz, by norm_num, by norm_num, by simpa using hT⟩, by simp⟩
  have hle := Finset.single_le_sum
    (f := fun ρ => (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ))
    (fun _ _ => by positivity) m
  have : (LeanLab.HelfgottMajor.ZeroCount1623.mult χ (1 / 2) : ℝ) ≤ 1 := hle.trans hsum
  exact_mod_cast this

end LeanLab.task783.RealZeroSum
