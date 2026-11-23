import LeanLab.task783.EndpointRealZeroLeaf

/-!
# Real zeros of primitive Dirichlet L-functions come in pairs beta, 1 - beta

AI wrote this code (Claude, a Claude Code subagent); it is not human reviewed.

Binary Goldbach is OPEN.  Nothing here bears on it directly.

This file records a check on the two leaves of `LeanLab.task783.EndpointRealZeroLeaf`.
By the functional equation for a primitive character and complex conjugation, a real zero
`β ∈ (0, 1)` of `L(s, χ)` forces `1 - β` to be a zero too.  Hence the leaf
`endpoint_real_zero_card_le_one`, which allows at most one real zero below the endpoint height,
forces every real zero in `(0, 1)` to equal `1 / 2`.  In particular it rules out a
Landau-Siegel zero for every primitive character of modulus at least 7, so that leaf is at least
as strong as an open problem.

Both theorems here are sorry free; (b) takes the leaf statement as a hypothesis and does not
use the leaf itself.
-/

namespace LeanLab.task783.RealZeroPairs

open Real Complex ComplexConjugate

variable {q : ℕ} [NeZero q]

private lemma gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; apply Gammaℝ_ne_zero_of_re_pos; simp; linarith

/-- The functional equation pairing of real zeros, Davenport chapter 9: for a primitive
character `χ` and a real zero `β ∈ (0, 1)` of `L(s, χ)`, the point `1 - β` is a zero too.
The proof passes through conjugation, `L(β, χ⁻¹) = conj L(β, χ)`, then the completed
functional equation `Λ(1 - s, χ) = q ^ (s - 1/2) ε(χ) Λ(s, χ⁻¹)`, using that the Gamma factor
does not vanish on the right half plane.  The case `q = 1` needs no special treatment since
`β ≠ 1` and `1 - β ≠ 0`. -/
theorem real_zero_one_sub (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {β : ℝ}
    (h0 : 0 < β) (h1 : β < 1) (hz : DirichletCharacter.LFunction χ β = 0) :
    DirichletCharacter.LFunction χ (1 - β) = 0 := by
  have hβ1 : (β : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  -- conjugation
  have hinv : DirichletCharacter.LFunction χ⁻¹ β = 0 := by
    have := LeanLab.HelfgottMajor.ZeroCount1623.LFunction_inv_conj χ hβ1
    rw [Complex.conj_ofReal] at this
    rw [this, hz, map_zero]
  -- completed L-function of χ⁻¹ vanishes at β
  have hβ0 : (β : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hΛ : DirichletCharacter.completedLFunction χ⁻¹ β = 0 := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (β : ℂ)
      (Or.inl hβ0)
    rw [hinv, eq_comm, div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h (gammaFactor_ne_zero _ (by simpa using h0))
  have hΛ' : DirichletCharacter.completedLFunction χ (1 - β) = 0 := by
    rw [hχ.completedLFunction_one_sub, hΛ, mul_zero]
  have h1β : (1 - (β : ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ _ (Or.inl h1β), hΛ',
    zero_div]

/-- The leaf `LeanLab.task783.endpoint_real_zero_card_le_one`, taken here as the hypothesis
`hcard`, implies that every real zero in `(0, 1)` equals `1 / 2`: it would pair with the
distinct zero `1 - β`.  So the leaf forbids a Landau-Siegel zero for every primitive character
of modulus at least 7, and is at least as strong as an open problem. -/
theorem real_zero_eq_half_of_card_le_one (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 * π ≤ (q : ℝ))
    (hcard : ((LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ (2 * π / q)).toFinset.filter
        (fun ρ => ρ.im = 0)).card ≤ 1)
    {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hz : DirichletCharacter.LFunction χ β = 0) :
    β = 1 / 2 := by
  have hT : 0 ≤ 2 * π / (q : ℝ) := by positivity
  have hz' := real_zero_one_sub χ hχ h0 h1 hz
  have m1 : (β : ℂ) ∈ ((LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ
      (2 * π / q)).toFinset.filter (fun ρ => ρ.im = 0)) := by
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨hz, by simpa using h0, by simpa using h1, by simpa using hT⟩, by simp⟩
  have m2 : ((1 - β : ℝ) : ℂ) ∈ ((LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ
      (2 * π / q)).toFinset.filter (fun ρ => ρ.im = 0)) := by
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨by push_cast; exact hz', by simp; linarith, by simp; linarith,
      by simpa using hT⟩, by simp⟩
  have heq := Finset.card_le_one.mp hcard _ m1 _ m2
  have : β = 1 - β := by exact_mod_cast heq
  linarith

end LeanLab.task783.RealZeroPairs
