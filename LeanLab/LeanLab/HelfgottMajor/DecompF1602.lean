import LeanLab.HelfgottMajor.DecompF547

/-!
Split of the exponential branch counting step `exp_branch_count_le` of DecompF547.lean,
FREE-nv-minimax task1602. No existing file is edited.

The target bounds the one sided multiplicity weighted exponential decay of the zero heights
of `L(·, χ)` inside the critical strip above height `T` against the exponential tail integral
`expTailIntegral`. The proof runs in three steps, and this file carries one leaf per step.

1. Shell counting. The zeros with positive imaginary part in a unit window above `T` number
   at most a logarithmic multiple of the window index, weighted by the analytic multiplicity.
2. Summability. The multiplicity weighted exponential decay series over those zeros is
   summable, because the shell count is logarithmic against the geometric decay.
3. Comparison. The total of the weighted series is at most the exponential tail integral,
   whose integrand is the same exponential decay against the zero density.

The assembly `exp_branch_count_le_F1602` has the statement of the target character for
character and is proved from the three leaves with no gap of its own. AI wrote this Lean
code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real

section DecompF1602

/-- LEAF. Shell counting step. The multiplicity weighted number of strip zeros of `L(·, χ)`
with positive imaginary part in the unit window `[n, n+1)` above height `T` is at most
`1600 * ((n+1) * (log (q*(n+1)) + 1))`. This is the one sided analogue of the shell count
used in the two sided exponential counting step, restricted to the positive imaginary part. -/
theorem exp_branch_shell_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (n : ℕ) (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      0 < ρ.im ∧ T < ρ.im ∧ ⌊ρ.im⌋₊ = n) :
    (∑ ρ ∈ s, (ZeroCount1623.mult χ ρ : ℝ)) ≤
      1600 * (((n : ℝ) + 1) * (Real.log ((q : ℝ) * ((n : ℝ) + 1)) + 1)) := by
  sorry

/-- LEAF. Summability step. The multiplicity weighted exponential decay series over the
strip zeros of `L(·, χ)` with positive imaginary part above height `T` is summable. The
absolute convergence comes from the logarithmic shell count against the geometric decay
`exp (-0.1598 * n)`; this step says nothing about the size of the total. -/
theorem exp_branch_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) := by
  sorry

/-- LEAF. Comparison step. The total of the multiplicity weighted exponential decay series
over the strip zeros of `L(·, χ)` with positive imaginary part above height `T` is at most
the exponential tail integral `expTailIntegral q T`, whose integrand is the same exponential
decay against the density `1/(2π) * log(q t / 2π) + 1/(4t)`. This is the quantitative half
of the branch, and it takes the summability of the weights as a hypothesis so that it is
only the size of the total. -/
theorem exp_branch_tsum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ≤
      TailIntegral123.expTailIntegral q T := by
  sorry

/-- Assembly of the split, FREE-nv-minimax task1602. The statement of
`exp_branch_count_le` character for character, proved from the three leaves with no gap
of its own: the summability leaf gives the first conjunct, and the comparison leaf closes
the second conjunct against `expTailIntegral`. -/
theorem exp_branch_count_le_F1602 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ≤
      TailIntegral123.expTailIntegral q T := by
  classical
  have hs := exp_branch_summable q χ T
  exact ⟨hs, exp_branch_tsum_le q χ T hs⟩

end DecompF1602

end LeanLab.HelfgottMajor.SplitGaussian123
