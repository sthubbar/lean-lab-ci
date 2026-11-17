import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le

/-!
Split of `positive_mass_window_one_norm_summable` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_one_le` into three leaves.

The statement being split says that the family of the Gaussian Mellin norms at the zeros of a
Dirichlet `L`-function in the open strip `0 < re < 1` below height `T` is summable. It carries no
hypothesis on the zeros, so the convergence has to come from the geometry of the zero set: below a
fixed height the relevant zeros sit in a closed ball, and a function whose zeros are isolated has
only finitely many of them there, after which a finite family is summable for free.

The split separates exactly those three steps. The first leaf is the bookkeeping that puts every
zero of the band inside the closed ball of radius `1 + T`: the real part is at most one and the
imaginary part is at most `T` in absolute value. The second leaf is the input the other two cannot
supply, the finiteness of the zero set inside that ball, which is where the isolatedness of the
zeros of the `L`-function on a compact set is spent. The third leaf is the passage from a finite
zero set to the summability of the norm family over it.

The assembly is the subset of the ball set by the band set, taken from the first two leaves, and
then the third leaf. It has no sorry of its own. All three leaves are OPEN.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3, the band sits in the closed ball. Every zero whose real part lies strictly
between zero and one and whose imaginary part is at most `T` in absolute value has norm at most
`1 + T`. This is the compactness bookkeeping that confines the band to a bounded region before
anything is said about finiteness: the real part contributes at most one, the imaginary part at
most `T`, and the two add. -/
theorem positive_mass_window_one_zero_norm_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (hT : 1 ≤ T) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (him : |ρ.im| ≤ T) :
    ‖ρ‖ ≤ 1 + T := by
  sorry

/-- LEAF 2 of 3, the zero set in the ball is finite. There are only finitely many zeros of the
`L`-function of modulus `q` in the closed ball of radius `1 + T` around the origin. This is the
one input the other two leaves cannot supply: the ball is compact, the `L`-function vanishes at
isolated points because it is not identically zero there, and a compact set with no accumulation
point of the zero set carries only finitely many of them. -/
theorem positive_mass_window_one_zero_set_closedBall_finite (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (hT : 1 ≤ T) :
    ({ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ ‖ρ‖ ≤ 1 + T}).Finite := by
  sorry

/-- LEAF 3 of 3, a finite band carries a summable family. If the zeros of the band form a finite
set, then the family of the Gaussian Mellin norms over them is summable: a family on a finite
index set is a finite sum, so it converges unconditionally, whatever the size of the individual
terms. No bound on the mass terms is needed here, only that the index set is finite. -/
theorem positive_mass_window_one_window_summable_of_finite (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T)
    (hfin : ({ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}).Finite) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  sorry

/-- The statement of `positive_mass_window_one_norm_summable`, proved from the three leaves.
The band set is a subset of the zero set in the closed ball by the first leaf, so the second leaf
makes it finite, and the third leaf turns that finiteness into summability of the norm family. -/
theorem positive_mass_window_one_norm_summable_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  have hball := positive_mass_window_one_zero_set_closedBall_finite q χ T hT
  have hsub : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} ⊆
      {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ ‖ρ‖ ≤ 1 + T} := by
    rintro ρ ⟨hzero, hre0, hre1, him⟩
    exact ⟨hzero, positive_mass_window_one_zero_norm_le q χ T hT hzero hre0 hre1 him⟩
  exact positive_mass_window_one_window_summable_of_finite q χ δ T hT (hball.subset hsub)

end LeanLab.HelfgottMajor.Decomp431a
