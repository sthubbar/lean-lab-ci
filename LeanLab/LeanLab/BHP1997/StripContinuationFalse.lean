/-
Refutation of `leaf_strip_continuation` in
LeanLab.BHP1997.SPLIT_leaf_strip_convexity_interpolation.

That leaf asserts that for every `x >= 2`, every modulus `1 <= q <= x` and EVERY Dirichlet
character `chi` of modulus `q`, the function `s |-> chi.LFunction s` is analytic on a
neighbourhood of each point of the closed strip `1 / 2 <= Re s <= 1 + 1 / log x`.

The point `s = 1` lies in that strip, and for the trivial character of any modulus `q`
Mathlib's `DirichletCharacter.LFunctionTrivChar_residue_one` gives
`(s - 1) * L(s, 1_q) -> prod_{p | q} (1 - 1 / p)` as `s -> 1`, a nonzero limit. An analytic
function is continuous, so analyticity at `1` would force that limit to be `0`. Hence the
leaf is false for the trivial character of every modulus, in particular for `q = 1`,
`x = 2`, where the function is the Riemann zeta function.

This file imports only Mathlib, states the leaf's statement verbatim, and proves its
negation. It has no sorry and adds no definition.

AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.StripContinuationFalse

open Complex Filter
open scoped Topology

/-- The residue `prod_{p | q} (1 - 1 / p)` of the trivial character L-function at `1` is
not zero, since no prime equals `1`. Standard. -/
theorem trivChar_residue_ne_zero (q : ℕ) :
    ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  have hp1 : (p : ℂ) ≠ 1 := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_one
  have hinv : (p : ℂ)⁻¹ ≠ 1 := fun h => hp1 (inv_eq_one.mp h)
  exact sub_ne_zero.mpr (Ne.symm hinv)

/-- The L-function of the trivial character of modulus `q` is not analytic at `s = 1`:
by `DirichletCharacter.LFunctionTrivChar_residue_one` it has a simple pole there with
nonzero residue, while analyticity would give continuity and so residue `0`. -/
theorem not_analyticAt_trivChar_one (q : ℕ) [NeZero q] :
    ¬ AnalyticAt ℂ (fun s : ℂ => (1 : DirichletCharacter ℂ q).LFunction s) 1 := by
  intro h
  have hc : ContinuousAt
      (fun s : ℂ => (s - 1) * (1 : DirichletCharacter ℂ q).LFunction s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul h.continuousAt
  have h0 : Tendsto (fun s : ℂ => (s - 1) * (1 : DirichletCharacter ℂ q).LFunction s)
      (𝓝[≠] 1) (𝓝 0) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({1} : Set ℂ)ᶜ))
    simpa using this
  have h1 := DirichletCharacter.LFunctionTrivChar_residue_one (N := q)
  exact trivChar_residue_ne_zero q (tendsto_nhds_unique h0 h1).symm

/-- For every `x >= 2` and every modulus `q`, the trivial character of modulus `q` violates
the conclusion of `leaf_strip_continuation`: the point `1` lies in the closed strip
`1 / 2 <= Re s <= 1 + 1 / log x` and the L-function is not analytic there. -/
theorem trivChar_not_analyticOnNhd_strip (x : ℝ) (hx : 2 ≤ x) (q : ℕ) [NeZero q] :
    ¬ AnalyticOnNhd ℂ (fun s : ℂ => (1 : DirichletCharacter ℂ q).LFunction s)
      {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 + 1 / Real.log x} := by
  intro h
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hinv : (0 : ℝ) < 1 / Real.log x := one_div_pos.mpr hlog
  refine not_analyticAt_trivChar_one q (h 1 ?_)
  refine ⟨?_, ?_⟩
  · simp only [one_re]; norm_num
  · simp only [one_re]; linarith

/-- The statement of `leaf_strip_continuation`, copied verbatim from
LeanLab.BHP1997.SPLIT_leaf_strip_convexity_interpolation, is FALSE. Counterexample:
`x = 2`, `q = 1`, `chi` the trivial character, whose L-function is the Riemann zeta
function with its pole at `s = 1` inside the strip. -/
theorem leaf_strip_continuation_false :
    ¬ (∀ (x : ℝ) (_ : 2 ≤ x) (q : ℕ) [NeZero q] (_ : 1 ≤ q) (_ : (q : ℝ) ≤ x)
        (χ : DirichletCharacter ℂ q),
        AnalyticOnNhd ℂ (fun s : ℂ => χ.LFunction s)
          {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 + 1 / Real.log x}) := by
  intro h
  exact trivChar_not_analyticOnNhd_strip 2 le_rfl 1
    (h 2 le_rfl 1 le_rfl (by norm_num) (1 : DirichletCharacter ℂ 1))

#print axioms trivChar_residue_ne_zero
#print axioms not_analyticAt_trivChar_one
#print axioms trivChar_not_analyticOnNhd_strip
#print axioms leaf_strip_continuation_false

end LeanLab.BHP1997.StripContinuationFalse
