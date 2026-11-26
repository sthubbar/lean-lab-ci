import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Split of `DQTailCountSplit.envelope_sum_le_stieltjes_count`, burst-20261124 S1,
tag dq_layer_split. P0014, Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4,
the Stieltjes summation after display 4.28 on page 38, used on page 41 for display 4.35.
The LEAF here is the summation step alone, with the two sided count N of t left as the
multiplicity sum over `ZeroCount1623.stripZeros`; no zero count is assumed. The count bound
of `MainTail123.zero_count_two_sided_of_book` is applied in `DQTailCountSplit`. No new
definitions.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DQTailLayerCake
open Real LeanLab.HelfgottMajor

/-- LEAF: P0014 page 38, the Stieltjes summation after display 4.28, as used on page 41 for
display 4.35, without pairing. Class HARD. For the decreasing envelope f with minus f prime
written out, the weighted sum over zeros above T is at most the integral over t above T of
minus f prime of t times N of t minus N of T. Route: f of abs gamma is the integral of
minus f prime over abs gamma to infinity, then Tonelli. Unconditional. -/
theorem envelope_sum_le_layer_cake
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) ≤
      ∫ t in Set.Ioi T,
        (0.1598 * exp (-0.1598 * t) +
          if δ = 0 then 0 else
            0.213 * t / (π * |δ|) ^ 2 * exp (-0.1065 * (t / (π * |δ|)) ^ 2)) *
        ((∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ t).toFinset,
            (ZeroCount1623.mult χ ρ : ℝ)) -
          ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ T).toFinset,
            (ZeroCount1623.mult χ ρ : ℝ)) := by
  sorry

end LeanLab.HelfgottMajor.DQTailLayerCake
