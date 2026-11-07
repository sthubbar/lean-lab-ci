/-
A split of `prop75`, the fully explicit major arc formula, into three leaves and an assembly.

The target bounds the second moment over `N ≤ X` of the error

  `rphi ϕ N - N 𝔖(N) - Mterm ϕ G N R T - Zterm ϕ G N R T`,

at `R = X ^ ϑ` and `T q = R ^ (-1/4) X q / R`, by `C (X ^ (3 - ϑ) + X ^ (13/5)) log X ^ 5`
for `0 < ϑ < 4/9`. Here `𝔖` is the singular series, `Mterm` the contribution of a single
zero with multiplicity and `Zterm` the contribution of a pair of zeros with multiplicities.

Write `I` for the integral over `α ∈ (0,1)` of `Sphi ϕ N α ^ 2` against the smoothed major arc
weight `bRhat G R T α` and `ee (-(N α))`. Then the error of the target is the sum of three
differences at every `N`,

  `(rphi ϕ N - I) + (I - N 𝔖(N) - Mterm) - Zterm`,

and the leaves estimate the three summands separately in mean square, each with the right hand
side shape of the target and its own implied constant. The three pieces are the three steps of
the argument: the smoothed integral against the arithmetic sum, the opening of the smoothed
integral into the singular series main term and the single zero sum, and the double zero sum.

* LEAF 1: `rphi ϕ N` against the smoothed major arc integral `I`, in mean square. This is the
  step in which the weights `bRhat` replace the sharp arcs, and it leaves the target's own
  right hand side shape with a constant of its own.
* LEAF 2: the smoothed major arc integral against the singular series main term together with
  the single zero sum `Mterm`, in mean square. The polar term at `q = 1` gives `N 𝔖(N)`, and
  each zero of a primitive character of conductor at most `R` gives its `Mterm` contribution.
* LEAF 3: the double zero sum `Zterm`, in mean square. This is the estimate that the pair of
  zeros with multiplicities can be summed in mean square at all, and it is the only leaf that
  needs the growth of `Iphi` in `N`.

The assembly `prop75_split` has no sorry and does not use `prop75`: it splits the error of the
target into the three differences above and adds the three mean square estimates. Every leaf
is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-- LEAF 1. Step one, the arithmetic sum against the smoothed major arc integral: there is `C`
such that for every `X ≥ 2` the second moment over `N ≤ X` of `rphi ϕ N` minus the integral of
`Sphi ϕ N α ^ 2` against `bRhat` at level `R = X ^ ϑ` and scale `T q = R ^ (-1/4) X q / R`, is
at most `C (X ^ (3 - ϑ) + X ^ (13/5)) log X ^ 5`. Both scale parameters are those of the
target, and only the first of the three differences is estimated. -/
theorem leaf_rphi_major (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) -
          ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  sorry

/-- LEAF 2. Step two, the smoothed major arc integral against the main term and the single
zero sum: there is `C` such that for every `X ≥ 2` the second moment over `N ≤ X` of the
integral of `Sphi ϕ N α ^ 2` against `bRhat` minus the singular series main term `N 𝔖(N)` and
minus `Mterm` at the same two scales, is at most `C (X ^ (3 - ϑ) + X ^ (13/5)) log X ^ 5`.
The pole of the `q = 1` term of the weight accounts for `N 𝔖(N)`, and every zero of every
primitive character of conductor at most `R` contributes its term of `Mterm`; no pair of
zeros is summed here. -/
theorem leaf_main_and_single_zero (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  sorry

/-- LEAF 3. Step three, the double zero sum: there is `C` such that for every `X ≥ 2` the
second moment over `N ≤ X` of `Zterm` at level `R = X ^ ϑ` and scale `T q = R ^ (-1/4) X q / R`
is at most `C (X ^ (3 - ϑ) + X ^ (13/5)) log X ^ 5`. This is the estimate that the pairs of
zeros with their multiplicities can be summed in mean square at all; it names no single zero
and no main term. -/
theorem leaf_zero_pair (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  sorry

/-- The square of a sum of two terms minus a third is at most three times the sum of the
squares: `‖x + y - z‖ ^ 2 ≤ 3 (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2)`. This is the only inequality
the assembly needs, and it is proved here. -/
private theorem norm_add_sub_sq_le75 (x y z : ℂ) :
    ‖x + y - z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have htri : ‖x + y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    have h1 : ‖x + y - z‖ ≤ ‖x + y‖ + ‖z‖ := by
      simpa using norm_sub_le (x + y) z
    have h2 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    linarith
  have hsq : ‖x + y - z‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul htri htri (norm_nonneg _) (by positivity)
  nlinarith [hsq, sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖y‖ - ‖z‖), sq_nonneg (‖x‖ - ‖z‖)]

/-- The fully explicit major arc formula, assembled from the three leaves above. The error of
the target is rewritten as `(rphi ϕ N - I) + (I - N 𝔖(N) - Mterm) - Zterm`, the private
lemma turns it into three squares, and the three mean square estimates are added; the constant
is three times the sum of the three leaf constants. -/
theorem prop75_split : Prop75 := by
  intro ϕ G hϕ hG ϑ hϑ0 hϑ
  obtain ⟨C₁, h₁⟩ := leaf_rphi_major ϕ G hϕ hG ϑ hϑ0 hϑ
  obtain ⟨C₂, h₂⟩ := leaf_main_and_single_zero ϕ G hϕ hG ϑ hϑ0 hϑ
  obtain ⟨C₃, h₃⟩ := leaf_zero_pair ϕ G hϕ hG ϑ hϑ0 hϑ
  refine ⟨3 * (C₁ + C₂ + C₃), ?_⟩
  intro X hX
  have hsum₁ := h₁ X hX
  have hsum₂ := h₂ X hX
  have hsum₃ := h₃ X hX
  have hpoint : ∀ N ∈ Finset.Icc 1 X,
      ‖(rphi ϕ N : ℂ) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        3 * (‖(rphi ϕ N : ℂ) -
              ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                bRhat G ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                ee (-(N * α))‖ ^ 2 +
            ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                bRhat G ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                ee (-(N * α))) - N * singular N -
              Mterm ϕ G N ((X : ℝ) ^ ϑ)
                (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 +
            ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
                (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2) := by
    intro N _
    have hsplit :
        (rphi ϕ N : ℂ) - N * singular N -
            Mterm ϕ G N ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
            Zterm ϕ G N ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) =
          ((rphi ϕ N : ℂ) -
              ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                bRhat G ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                ee (-(N * α))) +
            ((∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                bRhat G ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                ee (-(N * α))) - N * singular N -
              Mterm ϕ G N ((X : ℝ) ^ ϑ)
                (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)) -
            Zterm ϕ G N ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) := by
      ring
    rw [hsplit]
    exact norm_add_sub_sq_le75 _ _ _
  have hdecomp :
      ∑ N ∈ Finset.Icc 1 X,
          3 * (‖(rphi ϕ N : ℂ) -
                ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                  bRhat G ((X : ℝ) ^ ϑ)
                    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                  ee (-(N * α))‖ ^ 2 +
              ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                  bRhat G ((X : ℝ) ^ ϑ)
                    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                  ee (-(N * α))) - N * singular N -
                Mterm ϕ G N ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 +
              ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2) =
        3 * ((∑ N ∈ Finset.Icc 1 X,
              ‖(rphi ϕ N : ℂ) -
                ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                  bRhat G ((X : ℝ) ^ ϑ)
                    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                  ee (-(N * α))‖ ^ 2) +
          (∑ N ∈ Finset.Icc 1 X,
              ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                  bRhat G ((X : ℝ) ^ ϑ)
                    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                  ee (-(N * α))) - N * singular N -
                Mterm ϕ G N ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2) +
          (∑ N ∈ Finset.Icc 1 X,
              ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  calc ∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) - N * singular N -
            Mterm ϕ G N ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
            Zterm ϕ G N ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2
      ≤ ∑ N ∈ Finset.Icc 1 X,
          3 * (‖(rphi ϕ N : ℂ) -
                ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                  bRhat G ((X : ℝ) ^ ϑ)
                    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                  ee (-(N * α))‖ ^ 2 +
              ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                  bRhat G ((X : ℝ) ^ ϑ)
                    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                  ee (-(N * α))) - N * singular N -
                Mterm ϕ G N ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 +
              ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2) :=
        Finset.sum_le_sum hpoint
    _ = 3 * ((∑ N ∈ Finset.Icc 1 X,
              ‖(rphi ϕ N : ℂ) -
                ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                  bRhat G ((X : ℝ) ^ ϑ)
                    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                  ee (-(N * α))‖ ^ 2) +
          (∑ N ∈ Finset.Icc 1 X,
              ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
                  bRhat G ((X : ℝ) ^ ϑ)
                    (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
                  ee (-(N * α))) - N * singular N -
                Mterm ϕ G N ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2) +
          (∑ N ∈ Finset.Icc 1 X,
              ‖Zterm ϕ G N ((X : ℝ) ^ ϑ)
                  (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2)) := hdecomp
    _ ≤ 3 * ((C₁ * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) +
          (C₂ * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) +
          (C₃ * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5)) := by
        linarith [hsum₁, hsum₂, hsum₃]
    _ = 3 * (C₁ + C₂ + C₃) * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) *
          Real.log X ^ 5 := by
        ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_rphi_major

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_main_and_single_zero

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_zero_pair

#print axioms LeanLab.BhowmikGrimmelt2026.prop75_split
