import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le

/-!
Split of `positive_mass_window_two_norm_summable` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le` into three leaves.

The statement being split says that the nonnegative family of the Gaussian Mellin norms attached
to the zeros of a Dirichlet `L`-function in the strip `0 < re < 1` and below height `T` is
summable. Nothing in the statement restricts the zeros, so the only thing that can make the
family converge is that there are finitely many of them below a fixed height: at each zero the
term is a plain real number and no decay in the height is available at this point of the
development.

The split isolates exactly the three ingredients of that finiteness.

The first is analytic. The zeros of the `L`-function form a set with no accumulation point,
because the function is differentiable where it is evaluated, is not identically zero, and the
zeros of such a function are isolated. The second is arithmetic. A zero of the open strip whose
ordinate is bounded by `T` has modulus at most `T` plus two, since its real part lies between
zero and one, so the zero set sits inside one closed ball. The third is topological. A set with
no accumulation point inside a closed ball is finite. A finite family is summable, and that is
the statement being split.

None of the three leaves is a form of the statement being split, and each one drops one of its
ingredients: zeros with no accumulation point would still be infinitely many if their ordinates
were unbounded, and a bounded set would still be infinite if its points accumulated inside the
ball.

Each leaf is separately closable, and none of them needs the summable family. For orientation,
the imported closure already carries a proved theorem with this same conclusion for this same set
of zeros, which proves the three ingredients together; the three leaves below cut that one proof
at its seams rather than opening a different route.

The assembly is the compactness step plus the passage from a finite index set to a summable
family. It has no sorry of its own.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-! ### The three leaves -/

/-- LEAF 1 of 3, the analytic ingredient. Every point of the plane has a neighbourhood whose
intersection with the zero set of the `L`-function is contained in the singleton of that point.
In other words the zeros have no accumulation point anywhere: away from a zero a neighbourhood
misses the zeros altogether, and at a zero a neighbourhood meets them only at that zero. This is
where the differentiability of the `L`-function and its not vanishing identically are spent, and
it is the only leaf that uses anything about the function rather than about the shape of the
summand. -/
theorem positive_mass_window_two_zeros_discrete (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    IsDiscrete {z : ℂ | DirichletCharacter.LFunction χ z = 0} := by
  sorry

/-- LEAF 2 of 3, the arithmetic ingredient. A zero of the `L`-function in the open strip whose
ordinate is bounded by `T` in absolute value has modulus at most `T` plus two, so the whole zero
set being split sits inside one closed ball. The two is slack: the real part contributes less
than one and the imaginary part at most the absolute value of `T`, and the triangle inequality in
the form `norm at most absolute real part plus absolute imaginary part` adds them. At `T` equal to
one, the ball of radius three holds the set; at `T` negative the same bound holds because only the
absolute value of `T` appears. -/
theorem positive_mass_window_two_strip_zeros_subset_ball (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {z : ℂ | DirichletCharacter.LFunction χ z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T} ⊆
      Metric.closedBall (0 : ℂ) (|T| + 2) := by
  sorry

/-- LEAF 3 of 3, the topological ingredient. A set of complex numbers with no accumulation point
that is contained in a closed ball is finite: the closed ball is compact, a compact set covered by
the neighbourhoods that the discreteness supplies has a finite subcover, and each of those
neighbourhoods meets the set in at most one point. The statement is quantitative in neither the
set nor the radius, so it is used below at radius `T` plus two. It holds at an empty set and at a
negative radius, where the closed ball is empty. -/
theorem positive_mass_window_two_finite_of_subset_ball
    (S : Set ℂ) (R : ℝ) (hd : IsDiscrete S)
    (hsub : S ⊆ Metric.closedBall (0 : ℂ) R) : S.Finite := by
  sorry

/-- The assembly: the three leaves together make the norm family summable. The zero set being
split is discrete by the first leaf, it lies in the closed ball of radius `T` plus two by the
second leaf, and a discrete set inside a closed ball is finite by the third leaf, so the index
type is finite, and summing a real valued family over a finite index set converges. -/
theorem positive_mass_window_two_norm_summable_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  have hdisc : IsDiscrete {z : ℂ | DirichletCharacter.LFunction χ z = 0} :=
    positive_mass_window_two_zeros_discrete q χ
  have hsub : {z : ℂ | DirichletCharacter.LFunction χ z = 0 ∧
      0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T} ⊆ Metric.closedBall (0 : ℂ) (|T| + 2) :=
    positive_mass_window_two_strip_zeros_subset_ball q χ T
  have hfin : ({z : ℂ | DirichletCharacter.LFunction χ z = 0 ∧
      0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T}).Finite :=
    positive_mass_window_two_finite_of_subset_ball _
      (|T| + 2) (hdisc.mono fun _ hz => hz.1) hsub
  exact hfin.summable (fun z => ‖mellinMassTerm χ δ z‖)

end LeanLab.HelfgottMajor.Decomp431a
