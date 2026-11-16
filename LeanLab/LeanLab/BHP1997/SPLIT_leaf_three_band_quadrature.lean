/-
The quadrature of `leaf_three_band_quadrature` of `SPLIT_leaf_two_region_quadrature`: the split of
the integral of `1 / (a b^2)` over the three band union into five convex pieces.

The target asks for `13/10`. Its region is a disjunction of three bands, two of which carry a
further disjunction inside them. This file removes those inner disjunctions: it fixes five convex
pieces, each one fixed branch of one of the three bands, all of them inside the target region,
whose union carries an integral of about `1.3941`. The target is cut into

* `leaf_band_union_membership`, the geometric step: a point of one of the five fixed branches is a
  point of the target region. Linear arithmetic only.
* `leaf_band_union_quadrature`, the computation: the integral of `1 / (a b^2)` over the union of
  the five pieces is at least `13/10`. A floating point quadrature gives about `1.3941`, so the
  margin is about `0.094`; a grid sum over small rectangles inside each of the five pieces would
  prove it, since every piece is an explicit polygon cut out by rational linear inequalities.
* `leaf_band_union_integrand_bound`, the pointwise bound `1000` that the twofold monotonicity
  lemma needs for both integrands.

The assembly `leaf_three_band_quadrature_split` does nothing but compare the two integrands
pointwise, through the membership leaf and the nonnegativity of `1 / (a b^2)` on the region, apply
`slope_two_mono` and add the two numbers.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_two_region_quadrature

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

set_option maxHeartbeats 400000

/-- LEAF: the geometric step of the split. The first piece is the whole first band; the second and
third pieces are the two branches of the second band, distinguished by `a + b ≤ 7/16` against
`17/8 ≤ 4*a + 5*b`; the fourth and fifth pieces are the two branches of the third band,
distinguished by `4*a + b ≤ 15/8` against `17/8 ≤ 4*a + b`. Each piece repeats the branch
conditions of the band it comes from, so a point of any of them is a point of the target region,
with no use of the slack `ε` at all. -/
theorem leaf_band_union_membership (a b : ℝ) :
    (((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b)) →
    ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) := by
  sorry

/-- LEAF: the computation of the split. The integral of `1 / (a b^2)` over the union of the five
convex pieces is at least `13/10`; a floating point quadrature gives about `1.3941`, so there is a
margin of about `0.094` to spend on the rounding of any grid used for it. -/
theorem leaf_band_union_quadrature :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0) := by
  sorry

/-- LEAF: the pointwise bound. Each of the five pieces has `1/8 ≤ b ≤ a`, so `a b^2 ≥ 1/512` there
and its integrand is at most `512`; off the union the integrand is zero. Hence `1000` bounds it
everywhere. -/
theorem leaf_band_union_integrand_bound (a b : ℝ) :
    |(if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 := by
  sorry

/-- The quadrature of the target, assembled from the geometric step, the computation over the five
convex pieces and the pointwise bound: the union of the five pieces lies in the target region and
`1 / (a b^2) ≥ 0` there, so the two integrands are pointwise ordered, both are bounded by `1000`,
and `slope_two_mono` carries that order to the twofold iterated interval integrals. -/
theorem leaf_three_band_quadrature_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0 := by
  have hS : MeasurableSet {p : ℝ × ℝ | ((((((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧ p.1 + p.2 ≤ 7/16 ∧ 2273/10000 ≤ p.1)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 5*p.2 ∧ 2273/10000 ≤ p.1)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧ 4*p.1 + p.2 ≤ 15/8)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧ 17/8 ≤ 4*p.1 + p.2)))} := by
    have hle : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
        MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
    simp only [Set.ofPred_and, Set.ofPred_or]
    repeat' first
      | apply MeasurableSet.inter
      | apply MeasurableSet.union
      | (apply hle <;> fun_prop)
  have hf : Measurable (fun p : ℝ × ℝ =>
      if ((((((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧ p.1 + p.2 ≤ 7/16 ∧ 2273/10000 ≤ p.1)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 5*p.2 ∧ 2273/10000 ≤ p.1)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧ 4*p.1 + p.2 ≤ 15/8)) ∨ (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧ 17/8 ≤ 4*p.1 + p.2))) then 1/(p.1*p.2^2) else 0) :=
    Measurable.ite hS (by fun_prop) measurable_const
  have hR : MeasurableSet {p : ℝ × ℝ | ((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧
            (p.1 + p.2 ≤ 7/16 ∨ 17/8 ≤ 4*p.1 + 5*p.2) ∧
            (2273/10000 ≤ p.1 ∨ p.1 + 1/8 ≤ 2*p.2)) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧
            (4*p.1 + p.2 ≤ 15/8 ∨ 17/8 ≤ 4*p.1 + p.2)))} := by
    have hle : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
        MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
    simp only [Set.ofPred_and, Set.ofPred_or]
    repeat' first
      | apply MeasurableSet.inter
      | apply MeasurableSet.union
      | (apply hle <;> fun_prop)
  have hg : Measurable (fun p : ℝ × ℝ =>
      if ((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧
            (p.1 + p.2 ≤ 7/16 ∨ 17/8 ≤ 4*p.1 + 5*p.2) ∧
            (2273/10000 ≤ p.1 ∨ p.1 + 1/8 ≤ 2*p.2)) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧
            (4*p.1 + p.2 ≤ 15/8 ∨ 17/8 ≤ 4*p.1 + p.2))) then 1/(p.1*p.2^2) else 0) :=
    Measurable.ite hR (by fun_prop) measurable_const
  have hfM : ∀ a b : ℝ, |(if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 :=
    fun a b => leaf_band_union_integrand_bound a b
  have hgM : ∀ a b : ℝ, |(if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 :=
    fun a b => leaf_three_band_bound a b
  have hle' : ∀ a b : ℝ, (if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)
      ≤ (if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0) := by
    intro a b
    by_cases h : ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b)))
    · rw [if_pos h, if_pos (leaf_band_union_membership a b h)]
    · rw [if_neg h]
      by_cases hR : ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b)))
      · rw [if_pos hR]
        have hb1 : (1/8:ℝ) ≤ b := by
          rcases hR with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
          · linarith
          · exact h1
          · exact h1
        have hba : b ≤ a := by
          rcases hR with ⟨-, h2, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, -, h2, -⟩
          · exact h2
          · exact h2
          · exact h2
        have hb0 : (0:ℝ) < b := by linarith
        have ha0 : (0:ℝ) < a := by linarith
        positivity
      · rw [if_neg hR]
  have hm := slope_two_mono
    (fun a b => if ((((((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧ a + b ≤ 7/16 ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 5*b ∧ 2273/10000 ≤ a)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 4*a + b ≤ 15/8)) ∨ (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)
    (fun a b => if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)
    hf hg (M := 1000) hfM hgM hle' (lo := 1/10) (hi := 1/2) (by norm_num)
  have hq := leaf_band_union_quadrature
  linarith

end LeanLab.BHP1997.LowerShortC165
