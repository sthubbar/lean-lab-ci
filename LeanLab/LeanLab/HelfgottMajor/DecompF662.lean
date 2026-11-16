import LeanLab.HelfgottMajor.SPLIT_tail_mass_integral

/-!
Splitting the exponential counting step `Decomp269c.exp_count_le_integral` into two smaller
steps, FREE-nv-step task662.

The step bounds the total exponential weight of the zeros of `L(s, χ)` inside the critical
strip above height `T` by the density weighted exponential tail integral
`expTailIntegral`. The split separates

* the summability of the exponential weights over those zeros,
* the comparison of the total weight with the density weighted exponential tail integral,

and `exp_count_le_integral_F662` assembles them. The assembly does no analysis: it takes the
summability from the first leaf and feeds it to the second leaf, which closes the inequality.
Hence each step is one summability statement or one inequality, strictly weaker than the
assembled statement. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. The summability step of the exponential counting bound: the exponential weights
`exp (-0.1598 * |Im ρ|)` of the zeros of `L(·, χ)` inside the critical strip above height `T`
form a summable family. The absolute convergence comes from the logarithmic density of the
zeros against the geometric decay of the exponential; this step says nothing about the size
of the total. -/
theorem exp_count_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hT : 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => exp (-0.1598 * |ρ.val.im|)) := by
  sorry

/-- LEAF. The comparison step of the exponential counting bound: the total exponential weight
of the strip zeros above height `T` is at most the density weighted exponential tail integral
`expTailIntegral q T`. This is the quantitative half of the step, and it takes the summability
of the weights as a hypothesis so that it is only the size of the total. -/
theorem exp_count_tsum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hT : 100 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => exp (-0.1598 * |ρ.val.im|))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, exp (-0.1598 * |ρ.val.im|)) ≤
      expTailIntegral q T := by
  sorry

/-- Assembly. The exponential counting step, with the statement after the name repeated
character for character from `Decomp269c.exp_count_le_integral`. The first leaf gives the
summability and hands it to the second leaf, which closes the inequality against
`expTailIntegral`. The assembly itself proves every step from the leaves and has no gap. -/
theorem exp_count_le_integral_F662 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hT : 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => exp (-0.1598 * |ρ.val.im|)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, exp (-0.1598 * |ρ.val.im|)) ≤
      expTailIntegral q T := by
  have hs := exp_count_summable q χ T hT
  exact ⟨hs, exp_count_tsum_le q χ T hT hs⟩

end LeanLab.HelfgottMajor.Decomp269c
