import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import LeanLab.Halupczok2012.Feed1122SawtoothSumBound
import LeanLab.Halupczok2012.Feed1122HyperbolaIdentity

/-!
Split of `voronoi_divisor_sum_asymptotic` from Decomp532a.
Halupczok journal page 337, the Voronoi formula cited below display 2.2.
The classical proof is the Dirichlet hyperbola method followed by the
Voronoi, van der Corput bound for the sawtooth sum over divisors up to the square root.
Leaves: the exact hyperbola identity, the elementary harmonic sum reduction,
and the sawtooth exponential sum bound.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122VoronoiDivisorSumAsymptotic

open Finset

/-- Dirichlet hyperbola identity, formerly a leaf, the first step of the classical proof of the
Voronoi formula cited on Halupczok page 337. For every real x at least one,
the divisor summatory function equals twice the sum of floor x over m for m up to
the square root of x, minus the square of the floor of the square root.
Now carried by the integer leaf nat_hyperbola_identity in Feed1122HyperbolaIdentity. -/
theorem hyperbola_identity :
    ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) =
        2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (⌊x / m⌋₊ : ℝ) - (⌊Real.sqrt x⌋₊ : ℝ) ^ 2 :=
  Feed1122HyperbolaIdentity.hyperbola_identity_of_leaves

/-- LEAF: harmonic sum reduction in the classical proof of the Voronoi formula cited on
Halupczok page 337. Writing floor of x over m as x over m minus one half minus the
sawtooth, and using the harmonic sum up to the square root with Euler's constant,
the hyperbola expression differs from the main term plus minus twice the sawtooth sum by
a bounded amount, here stated with the weaker bound C x to one third log x.
Class MEDIUM: elementary real analysis with the Euler Mascheroni asymptotic. -/
theorem harmonic_reduction :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x →
      |(2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (⌊x / m⌋₊ : ℝ) - (⌊Real.sqrt x⌋₊ : ℝ) ^ 2) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
        2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / m) - 1 / 2)| ≤
          C * x ^ (1 / 3 : ℝ) * Real.log x := by
  sorry

/-- Voronoi sawtooth bound, formerly a leaf, the analytic step of the classical proof of the
Voronoi formula cited on Halupczok page 337. The sum over m up to the square root of x
of the sawtooth Int.fract of x over m minus one half is O of x to one third times log x,
proved by the van der Corput second derivative test on dyadic blocks.
Analytic content: a genuine exponential sum estimate.
Now carried by the smaller HARD leaf tail_sawtooth_bound in Feed1122SawtoothSumBound. -/
theorem sawtooth_sum_bound :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x →
      |∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / m) - 1 / 2)| ≤
        C * x ^ (1 / 3 : ℝ) * Real.log x :=
  Feed1122SawtoothSumBound.sawtooth_sum_bound_of_leaves

/-- The hyperbola identity and the harmonic reduction give the divisor sum
minus the main term plus twice the sawtooth sum, at size x to one third log x. -/
theorem divisor_sum_sawtooth_form :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
        2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / m) - 1 / 2)| ≤
          C * x ^ (1 / 3 : ℝ) * Real.log x := by
  obtain ⟨C, X0, hC, h⟩ := harmonic_reduction
  refine ⟨C, max X0 1, hC, fun x hx => ?_⟩
  rw [hyperbola_identity x ((le_max_right _ _).trans hx)]
  exact h x ((le_max_left _ _).trans hx)

/-- Halupczok journal page 337, the printed Voronoi formula below display 2.2,
assembled from the three leaves. Statement identical to the parent declaration. -/
theorem voronoi_divisor_sum_asymptotic_of_leaves :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)| ≤
          C * x ^ (1 / 3 : ℝ) * Real.log x := by
  obtain ⟨CA, XA, hCA, hA⟩ := divisor_sum_sawtooth_form
  obtain ⟨CB, XB, hCB, hB⟩ := sawtooth_sum_bound
  refine ⟨CA + 2 * CB, max (max XA XB) 2, by positivity, le_max_right _ _, fun x hx => ?_⟩
  have hA' := hA x ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  have hB' := hB x ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  obtain ⟨a1, a2⟩ := abs_le.mp hA'
  obtain ⟨b1, b2⟩ := abs_le.mp hB'
  have he : (CA + 2 * CB) * x ^ (1 / 3 : ℝ) * Real.log x =
      CA * x ^ (1 / 3 : ℝ) * Real.log x + 2 * (CB * x ^ (1 / 3 : ℝ) * Real.log x) := by ring
  rw [he]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end LeanLab.Halupczok2012.Feed1122VoronoiDivisorSumAsymptotic

#print axioms LeanLab.Halupczok2012.Feed1122VoronoiDivisorSumAsymptotic.divisor_sum_sawtooth_form
#print axioms LeanLab.Halupczok2012.Feed1122VoronoiDivisorSumAsymptotic.voronoi_divisor_sum_asymptotic_of_leaves
