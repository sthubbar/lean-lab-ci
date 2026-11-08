import LeanLab.HelfgottMajor.DecompJ1153

/-!
Split of the open Gaussian moment bound of this folder.

The target bounds the square root of `gaussianMomentSum` by `sqrt Sec45.nTwo * sqrt T`
plus `sqrt Sec45.nLog * sqrt T`.  The split separates the three ingredients of the
argument: the two squared `L2` energies `nTwo` and `nLog` are nonnegative; pulling the
height factor `T` out of the zero sum and bounding the remaining sum of multiplicities
times squared Mellin norms by their sum gives the moment sum at most `(nTwo + nLog) * T`;
and the square root of a sum of two nonnegative terms is at most the sum of the square
roots, once the common height factor is taken out.  The assembly at the end of the file
is exactly those three steps and has no `sorry` of its own.
-/

namespace LeanLab.HelfgottMajor.DecompJ1153
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF. The two `L2` energies of the Gaussian profile and of its logarithm, which are the
closed forms `Sec45.nTwo` and `Sec45.nLog`, are nonnegative: both are square integrals of a
norm, and the height `T` is at least one, so `sqrt T` is defined and positive. -/
theorem leaf_plancherel_constants_nonneg : 0 ≤ Sec45.nTwo ∧ 0 ≤ Sec45.nLog := by
  constructor
  · unfold Sec45.nTwo
    positivity
  · exact Sec45.nLog_nonneg

/-- LEAF. Moment sum step.  Every zero in the middle range has `1 < |im| ≤ T`, its
multiplicity is a nonnegative natural number, and the squared Mellin norm is nonnegative, so
the zero sum is at most `T` times a sum of multiplicities times squared norms; the Plancherel
identities for the Gaussian profile give `Sec45.nTwo` and its logarithm gives
`Sec45.nLog`, and the two ranges `1 < |im|` and the weight `log |ρ|` contribute at most their
sum.  This is the analytic content of the bound. -/
theorem leaf_moment_plancherel_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    gaussianMomentSum χ δ T ≤ (Sec45.nTwo + Sec45.nLog) * T := by
  -- BLOCKED OUT OF REACH. The missing result is a discrete sampling inequality for
  -- Dirichlet L function zeros that converts the continuous Gaussian Mellin energies
  -- into the weighted zero sum in this statement. Mathlib has no such inequality.
  -- Own attempt error: linarith failed to find a contradiction at the missing bound
  -- from multiplicity times squared Mellin norm to Sec45.nTwo plus Sec45.nLog.
  sorry

/-- LEAF. Elementary square root step: for nonnegative `a`, `b` and `T`, the square root of
`a + b` times the square root of `T` is at most the sum of the two separate square root
terms.  Nothing about the sizes of `a` and `b` is used beyond nonnegativity. -/
theorem leaf_sqrt_sum_le (a b T : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T) :
    sqrt (a + b) * sqrt T ≤ sqrt a * sqrt T + sqrt b * sqrt T := by
  have hprod : 0 ≤ sqrt a * sqrt b :=
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hsq : (sqrt a + sqrt b) ^ 2 = a + b + 2 * sqrt a * sqrt b := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    ring
  have hle : a + b ≤ (sqrt a + sqrt b) ^ 2 := by
    nlinarith [hprod]
  have hsum0 : 0 ≤ sqrt a + sqrt b :=
    add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hroot : sqrt (a + b) ≤ sqrt ((sqrt a + sqrt b) ^ 2) :=
    Real.sqrt_le_sqrt hle
  have hsqrt : sqrt (a + b) ≤ sqrt a + sqrt b := by
    rw [Real.sqrt_sq hsum0] at hroot
    exact hroot
  simpa [add_mul] using
    mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg T)

/-- Assembly of the split: the moment sum is at most `(nTwo + nLog) * T` and the square root
of that is at most the sum of the two square root terms. -/
theorem gaussian_moment_sum_bound_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    sqrt (gaussianMomentSum χ δ T) ≤ sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T := by
  obtain ⟨hTwo, hLog⟩ := leaf_plancherel_constants_nonneg
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have h1 := leaf_moment_plancherel_bound q χ δ T hT
  calc sqrt (gaussianMomentSum χ δ T)
      ≤ sqrt ((Sec45.nTwo + Sec45.nLog) * T) := Real.sqrt_le_sqrt h1
    _ = sqrt (Sec45.nTwo + Sec45.nLog) * sqrt T := Real.sqrt_mul (add_nonneg hTwo hLog) T
    _ ≤ sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T :=
        leaf_sqrt_sum_le Sec45.nTwo Sec45.nLog T hTwo hLog hT0

end LeanLab.HelfgottMajor.DecompJ1153
