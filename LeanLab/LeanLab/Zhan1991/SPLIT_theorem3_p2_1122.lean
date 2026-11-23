import LeanLab.Zhan1991.SPLIT_theorem3_1122

/-!
P0068 Zhan 1991, page 269, the next split step under the two range LEAFs of
SPLIT_theorem3_1122, burst-20261122, session S80.

Both ranges of (3.19) apply Lemma 4 to a window `[T₁, T₁ + H]` that may violate `H ≥ |T₁|^{1/3}`,
so the window must be enlarged, which needs the count `N(α, T, H, q)` to be monotone in `H`;
the high range also needs "no zero in the region gives count 0", where the junk value of the
principal `L(s, χ₀)` at the pole `s = 1` must not count. The second is PROVED outright; the
first is PROVED from one LEAF, the finiteness of the zero sets.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open Filter Topology

/-- LEAF: Page 262, Lemma 4, the count `N(α, T, H, q)` is a finite count: for `α ≥ 1/2` the zeros
of `L(s, χ)` with `Re s ≥ α` and `T ≤ Im s ≤ T + H` form a finite set. MEDIUM: `L(s, χ)` is
analytic off `s = 1` and not identically zero, its zeros are isolated, there is none with
`Re s ≥ 1` except possibly the junk value at the pole, and none accumulates at the pole. -/
theorem zeroWindow_finite (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (α T H : ℝ)
    (hα : 1 / 2 ≤ α) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
      ρ.im ≤ T + H}.Finite := by
  sorry

/-- Page 262, Lemma 5 is about zeros, not the pole: the order of `L(s, χ)` at `s = 1` is `0`
for every `χ`. For `χ ≠ χ₀` this is `L(1, χ) ≠ 0`; for `χ₀` the function is not analytic at
`s = 1`, since its residue `∏_{p ∣ q} (1 - p⁻¹)` is not `0`. PROVED. -/
theorem analyticOrderNat_LFunction_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) 1 = 0 := by
  by_cases hχ : χ = 1
  · subst hχ
    apply analyticOrderNatAt_of_not_analyticAt
    intro han
    have hc : ContinuousAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) 1 :=
      han.continuousAt
    have h0 : Tendsto (fun s : ℂ => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)
        (𝓝[≠] 1) (𝓝 0) := by
      have : Tendsto (fun s : ℂ => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)
          (𝓝 1) (𝓝 ((1 - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) 1)) :=
        ((continuous_id.sub continuous_const).continuousAt.tendsto).mul hc.tendsto
      simpa using this.mono_left nhdsWithin_le_nhds
    have hr := DirichletCharacter.LFunctionTrivChar_residue_one (N := q)
    have heq := tendsto_nhds_unique hr h0
    have hne : ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      intro h
      have : (p : ℂ)⁻¹ = 1 := by linear_combination -h
      have : (p : ℂ) = 1 := by simpa using congrArg (·⁻¹) this
      have : (p : ℝ) = 1 := by exact_mod_cast this
      linarith
    exact hne heq
  · unfold analyticOrderNatAt
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (DirichletCharacter.LFunction_apply_one_ne_zero hχ))]
    rfl

/-- Page 269, window enlargement: `N(α, T, H, q)` is monotone in `H`. PROVED, CONDITIONAL ON
the finiteness of the larger windows. -/
theorem zeroCountZ_mono_H_of (q : ℕ) [NeZero q] (α T H H' : ℝ) (hH : H ≤ H')
    (hfinite : ∀ χ : DirichletCharacter ℂ q, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H'}.Finite) :
    zeroCountZ α T H q ≤ zeroCountZ α T H' q := by
  unfold zeroCountZ
  apply Finset.sum_le_sum
  intro χ _
  set s := {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
      ρ.im ≤ T + H}
  set s' := {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
      ρ.im ≤ T + H'}
  have hss : s ⊆ s' := by
    intro ρ hρ
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans (by linarith)⟩
  have hfin : s'.Finite := hfinite χ
  set g := fun ρ : ℂ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
  have hg0 : ∀ ρ, 0 ≤ g ρ := fun ρ => Nat.cast_nonneg _
  rw [finsum_mem_def, finsum_mem_def]
  apply finsum_le_finsum
  · exact (hfin.subset hss).subset (Set.support_indicator_subset)
  · exact hfin.subset (Set.support_indicator_subset)
  · intro ρ
    exact Set.indicator_le_indicator_of_subset hss hg0 ρ

/-- Page 269, "by (2.4) and Lemma 5": when no zero other than `s = 1` lies in the region, the
count is `0`. PROVED, CONDITIONAL ON the order at `s = 1` being `0`. -/
theorem zeroCountZ_eq_zero_of_free_of (q : ℕ) [NeZero q] (α T H : ℝ)
    (hone : ∀ χ : DirichletCharacter ℂ q,
      analyticOrderNatAt (DirichletCharacter.LFunction χ) 1 = 0)
    (hfree : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), ρ ≠ 1 →
      DirichletCharacter.LFunction χ ρ = 0 → α ≤ ρ.re → T ≤ ρ.im → ρ.im ≤ T + H → False) :
    zeroCountZ α T H q = 0 := by
  unfold zeroCountZ
  apply Finset.sum_eq_zero
  intro χ _
  apply finsum_mem_eq_zero_of_forall_eq_zero
  intro ρ hρ
  by_cases h1 : ρ = 1
  · subst h1
    simp [hone χ]
  · exact (hfree χ ρ h1 hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2).elim

/-- `zeroCountZ_mono_H_of` wired through the LEAF `zeroWindow_finite`. -/
theorem zeroCountZ_mono_H (q : ℕ) [NeZero q] (α T H H' : ℝ) (hα : 1 / 2 ≤ α) (hH : H ≤ H') :
    zeroCountZ α T H q ≤ zeroCountZ α T H' q :=
  zeroCountZ_mono_H_of q α T H H' hH fun χ => zeroWindow_finite q χ α T H' hα

/-- `zeroCountZ_eq_zero_of_free_of` wired through the LEAF `analyticOrderNat_LFunction_one`. -/
theorem zeroCountZ_eq_zero_of_free (q : ℕ) [NeZero q] (α T H : ℝ)
    (hfree : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), ρ ≠ 1 →
      DirichletCharacter.LFunction χ ρ = 0 → α ≤ ρ.re → T ≤ ρ.im → ρ.im ≤ T + H → False) :
    zeroCountZ α T H q = 0 :=
  zeroCountZ_eq_zero_of_free_of q α T H (analyticOrderNat_LFunction_one q) hfree

end

end LeanLab.Zhan1991
