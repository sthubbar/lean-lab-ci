import LeanLab.HelfgottMajor.DecompF662

/-!
Splitting the exponential counting comparison `DecompF662.exp_count_tsum_le` into smaller
steps, FREE-nv-step task1605.

The step bounds the total exponential weight of the zeros of `L(s, χ)` inside the critical
strip above height `T` by the density weighted exponential tail integral
`expTailIntegral`. The split separates

* the reduction of the zero sum to a discrete shell series via the zero count,
* the comparison of the shell series with the tail integral,

and `exp_count_tsum_le_F1605` assembles them. Each leaf is one inequality, strictly weaker
than the assembled statement. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. The zero sum is bounded by a discrete shell series: grouping the zeros by the
integer part of `|Im ρ|`, the total exponential weight is at most the sum over shells of
`6400 * (q+1) * (n²+1) * exp (-0.1598 * n)`. This is the counting input from the zero
density, and it reduces the continuous zero set to a summable series over `ℕ`. -/
theorem exp_count_tsum_le_shell_series (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hT : 100 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => exp (-0.1598 * |ρ.val.im|))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, exp (-0.1598 * |ρ.val.im|)) ≤
      6400 * ((q : ℝ) + 1) * (∑' n : ℕ, (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ)))) := by
  sorry

/-- LEAF. The shell series is bounded by the tail integral: for `T ≥ 100`, the series
`6400 * (q+1) * ∑' n (n²+1) * exp (-0.1598 * n)` is at most `expTailIntegral q T`.
This is the comparison of the discrete shell series with the continuous density weighted
integral, closing the argument. -/
theorem shell_series_le_expTailIntegral (q : ℕ) [NeZero q] (T : ℝ) (hT : 100 ≤ T) :
    6400 * ((q : ℝ) + 1) * (∑' n : ℕ, (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ)))) ≤
      expTailIntegral q T := by
  sorry

/-- The exponential counting comparison, with the statement after the name repeated
character for character from `DecompF662.exp_count_tsum_le`. The assembly chains the
two leaves: the zero sum is bounded by the shell series, and the shell series is bounded
by the tail integral. -/
theorem exp_count_tsum_le_F1605 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hT : 100 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => exp (-0.1598 * |ρ.val.im|))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, exp (-0.1598 * |ρ.val.im|)) ≤
      expTailIntegral q T := by
  have h1 := exp_count_tsum_le_shell_series q χ T hT hs
  have h2 := shell_series_le_expTailIntegral q T hT
  exact le_trans h1 h2

end LeanLab.HelfgottMajor.Decomp269c
