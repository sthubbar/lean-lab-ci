import LeanLab.task783.RealZeroSum

/-!
# Off line zeros in the positive imaginary window come in pairs

A check on the leaf `Decomp388a.endpoint_positive_im_sum_le` of
`HelfgottMajor/SPLIT_endpoint_strip_sum_le`, which bounds by `2` the multiplicity weighted count
of the strip zeros of a primitive `L(s, χ)` with `0 < Im ρ ≤ 2π/q`.

By the functional equation for a primitive character together with complex conjugation,
Davenport chapter 9, a strip zero `ρ` of `L(s, χ)` forces `1 - conj ρ` to be a zero of the same
`L(s, χ)`, at the same height `Im ρ`.  So the window `0 < Im ρ ≤ T` of strip zeros is closed under
`ρ ↦ 1 - conj ρ`, `strip_window_one_sub_conj_mem`.  Hence the leaf, taken here only as the
hypothesis `hsum`, says: if the window holds a zero off the critical line, the window consists of
exactly that zero and its partner, `window_eq_pair_of_off_line`, so no zero on the critical line
lies below height `2π/q` together with an off line one.  Nothing here uses the leaf itself; both
theorems are sorry free, and the leaf stays open, see the note of S2-06 in burst-20261124.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.EndpointPositiveImPairs

open Real Complex ComplexConjugate

variable {q : ℕ} [NeZero q]

private lemma gammaFactor_ne_zero' {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; apply Gammaℝ_ne_zero_of_re_pos; simp; linarith

/-- The functional equation pairing of strip zeros, Davenport chapter 9: for a primitive
character `χ` and a zero `ρ` of `L(s, χ)` with `0 < Re ρ < 1`, the point `1 - conj ρ` is a zero
of the same `L(s, χ)`.  Through `L(conj ρ, χ⁻¹) = conj L(ρ, χ)` and the completed functional
equation `Λ(1 - s, χ) = ε q^{...} Λ(s, χ⁻¹)` at `s = conj ρ`. -/
theorem strip_zero_one_sub_conj (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ (1 - conj ρ) = 0 := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hinv : DirichletCharacter.LFunction χ⁻¹ (conj ρ) = 0 := by
    rw [LeanLab.HelfgottMajor.ZeroCount1623.LFunction_inv_conj χ hρ1, hz, map_zero]
  have hρ0 : conj ρ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hΛ : DirichletCharacter.completedLFunction χ⁻¹ (conj ρ) = 0 := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (conj ρ)
      (Or.inl hρ0)
    rw [hinv, eq_comm, div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h (gammaFactor_ne_zero' _ (by simpa using h0))
  have hΛ' : DirichletCharacter.completedLFunction χ (1 - conj ρ) = 0 := by
    rw [hχ.completedLFunction_one_sub, hΛ, mul_zero]
  have h1ρ : (1 - conj ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ _ (Or.inl h1ρ), hΛ',
    zero_div]

/-- The window of strip zeros with `0 < Im ρ` below height `T` is closed under `ρ ↦ 1 - conj ρ`,
which keeps `Im ρ` and sends `Re ρ` to `1 - Re ρ`. -/
theorem strip_window_one_sub_conj_mem (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ T).toFinset.filter
      (fun ρ => 0 < ρ.im)) :
    (1 - conj ρ) ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ T).toFinset.filter
      (fun ρ => 0 < ρ.im) := by
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset,
    LeanLab.HelfgottMajor.ZeroCount1623.stripZeros, Set.mem_setOf_eq] at hρ ⊢
  obtain ⟨⟨hz, h0, h1, hT⟩, him⟩ := hρ
  refine ⟨⟨strip_zero_one_sub_conj χ hχ h0 h1 hz, ?_, ?_, ?_⟩, ?_⟩
  · simp; linarith
  · simp; linarith
  · simpa using hT
  · simpa using him

/-- The leaf `Decomp388a.endpoint_positive_im_sum_le`, taken here as the hypothesis `hsum` for a
general height `T`, forces: once the window `0 < Im ρ ≤ T` holds a zero `ρ` off the critical
line, every zero of the window is `ρ` or its partner `1 - conj ρ`. -/
theorem window_eq_pair_of_off_line (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hsum : (∑ ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ T).toFinset.filter
        (fun ρ => 0 < ρ.im), (LeanLab.HelfgottMajor.ZeroCount1623.mult χ ρ : ℝ)) ≤ 2)
    {ρ : ℂ}
    (hρ : ρ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ T).toFinset.filter
      (fun ρ => 0 < ρ.im))
    (hoff : ρ.re ≠ 1 / 2) :
    ∀ σ ∈ (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ T).toFinset.filter
      (fun ρ => 0 < ρ.im), σ = ρ ∨ σ = 1 - conj ρ := by
  set W := (LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ T).toFinset.filter
      (fun ρ => 0 < ρ.im) with hW
  intro σ hσ
  by_contra hne
  push_neg at hne
  obtain ⟨hσρ, hσρ'⟩ := hne
  have hρ' := strip_window_one_sub_conj_mem χ hχ hρ
  have hpair : ρ ≠ 1 - conj ρ := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hoff (by linarith)
  have hmult : ∀ x ∈ W, (1 : ℝ) ≤ (LeanLab.HelfgottMajor.ZeroCount1623.mult χ x : ℝ) := by
    intro x hx
    rw [hW] at hx
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset,
      LeanLab.HelfgottMajor.ZeroCount1623.stripZeros, Set.mem_setOf_eq] at hx
    exact_mod_cast LeanLab.task783.RealZeroSum.mult_pos χ hx.1.1 hx.1.2.2.1
  have hsub : ({ρ, 1 - conj ρ, σ} : Finset ℂ) ⊆ W := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hρ
    · exact hρ'
    · exact hσ
  have h3 : (3 : ℝ) ≤ ∑ x ∈ ({ρ, 1 - conj ρ, σ} : Finset ℂ),
      (LeanLab.HelfgottMajor.ZeroCount1623.mult χ x : ℝ) := by
    rw [Finset.sum_insert (by simp [hpair, hσρ.symm]),
      Finset.sum_insert (by simp [hσρ'.symm]), Finset.sum_singleton]
    have a := hmult ρ hρ
    have b := hmult _ hρ'
    have c := hmult σ hσ
    linarith
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x => (LeanLab.HelfgottMajor.ZeroCount1623.mult χ x : ℝ))
    (fun _ _ _ => Nat.cast_nonneg _)
  linarith

end LeanLab.HelfgottMajor.EndpointPositiveImPairs
