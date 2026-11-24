import LeanLab.HelfgottMajor.FALSE_feed1122_exp_branch_tsum_le

/-!
Conditional refutation of `SplitGaussian123.exp_branch_count_le` of DecompF547.lean,
feed burst 20261122. No existing file is edited.

The leaf has no hypothesis on the cutoff T. At T zero the Lean tail integral
`TailIntegral123.expTailIntegral q 0` is zero, because its integrand carries the term
exp of minus 0.1598 t times 1 over 4t, which is not integrable near zero; this is
`Feed1122ExpBranch.expTailIntegral_zero`, proved. The left side is a sum of nonnegative terms,
positive as soon as `L(·, χ)` has one zero in the open strip with positive imaginary part.
So the leaf fails at T zero for every such character: either the family is not summable, and
the first conjunct fails, or it is summable, and one positive term already exceeds zero.

For q one the character is trivial and `L` is the Riemann zeta function, with the zero near
1/2 + 14.1347 i; Mathlib does not record any nontrivial zeta zero, so its existence is the
explicit hypothesis `hzero`. Independently, notes/burst-20261122/HelfgottMajor-tail_branch_audit.md
found the inequality false for positive cutoffs too, q one and T 101.3, 103.7 or 150,
ratio up to 1.25, falsifier AGREE: the bare density omits the boundary term that page 38 of
P0014 drops after display 4.28.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ExpBranchCount
open Real

/-- Conditional refutation of `exp_branch_count_le` at cutoff zero, for any character whose
`L` function has a zero in the open critical strip with positive imaginary part. -/
theorem FALSE_feed1122_exp_branch_count_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hzero : ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im) :
    ¬ (Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ (0 : ℝ) < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ∧
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ (0 : ℝ) < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ≤
        TailIntegral123.expTailIntegral q 0) := by
  rintro ⟨hs, hle⟩
  obtain ⟨ρ, hρ, h0, h1, him⟩ := hzero
  rw [Feed1122ExpBranch.expTailIntegral_zero] at hle
  let ρ' : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ (0 : ℝ) < ρ.im} := ⟨ρ, hρ, h0, h1, him, him⟩
  have hterm := hs.le_tsum ρ' (fun _ _ => by positivity)
  have hm : (1 : ℝ) ≤ (ZeroCount1623.mult χ ρ : ℝ) := by
    exact_mod_cast Feed1122ExpBranch.one_le_mult_feed χ hρ h1
  have hpos : 0 < (ZeroCount1623.mult χ ρ : ℝ) * Real.exp (-0.1598 * ρ.im) :=
    mul_pos (by linarith) (Real.exp_pos _)
  have : (ZeroCount1623.mult χ ρ'.val : ℝ) * Real.exp (-0.1598 * ρ'.val.im) ≤ 0 :=
    hterm.trans hle
  exact absurd this (not_le.mpr hpos)

/-- The same refutation phrased against the universally quantified sealed statement. -/
theorem FALSE_feed1122_exp_branch_count_le_forall (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hzero : ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im) :
    ¬ ∀ T : ℝ,
      Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ∧
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ≤
        TailIntegral123.expTailIntegral q T :=
  fun h => FALSE_feed1122_exp_branch_count_le q χ hzero (h 0)

end LeanLab.HelfgottMajor.Feed1122ExpBranchCount

