import LeanLab.HelfgottMajor.DecompJ1153

/-!
Split of `DecompJ1153.gaussian_moment_sum_bound` into leaf lemmas.

The target bounds the square root of `gaussianMomentSum` by
`(sqrt nTwo * sqrt T + sqrt nLog * sqrt T) * sqrt (log (q * T))`.
The split separates the analytic bound on the moment sum itself from the
elementary square root inequality that distributes the square root over a sum.

The assembly `gaussian_moment_sum_bound_F1606` chains those two steps and has
no `sorry` of its own.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DecompF1606
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b DecompJ1153

/-- LEAF. The core analytic inequality: the Gaussian moment sum over zeros
with `1 < |im| ≤ T` is at most `(nTwo + nLog) * T * log (q * T)`.
This is the partial summation step of P0014 pages 38 to 40, displays 4.26 and 4.31,
combined with the Plancherel identities of display 4.42 on page 43.
Each zero contributes multiplicity times `|im|` times the squared Mellin norm;
pulling out the height factor `T` and bounding the remaining sum by the two
L2 energies gives the product. -/
theorem leaf_gaussian_moment_sum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    gaussianMomentSum χ δ T ≤ (Sec45.nTwo + Sec45.nLog) * T * log (q * T) := by
  sorry

/-- LEAF. Elementary square root inequality: for nonnegative `a` and `b`,
`sqrt (a + b) ≤ sqrt a + sqrt b`. This is the step that distributes the square
root over the sum of the two L2 energies. -/
theorem leaf_sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sqrt (a + b) ≤ sqrt a + sqrt b := by
  have hprod : 0 ≤ sqrt a * sqrt b :=
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hsq : (sqrt a + sqrt b) ^ 2 = a + b + 2 * sqrt a * sqrt b := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    ring
  have hle : a + b ≤ (sqrt a + sqrt b) ^ 2 := by
    nlinarith
  have hsum0 : 0 ≤ sqrt a + sqrt b :=
    add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hroot : sqrt (a + b) ≤ sqrt ((sqrt a + sqrt b) ^ 2) :=
    Real.sqrt_le_sqrt hle
  rw [Real.sqrt_sq hsum0] at hroot
  exact hroot

/-- LEAF. The first L2 energy `Sec45.nTwo` is nonnegative. It is defined as
`√π / 2`, a product of nonnegative factors. -/
theorem leaf_nTwo_nonneg : 0 ≤ Sec45.nTwo := by
  unfold Sec45.nTwo
  positivity

/-- LEAF. The second L2 energy `Sec45.nLog` is nonnegative. This is already
proved in `Sec45.nLog_nonneg`, restated here as a leaf for the assembly. -/
theorem leaf_nLog_nonneg : 0 ≤ Sec45.nLog :=
  Sec45.nLog_nonneg

/-- Assembly of the split: the moment sum is at most `(nTwo + nLog) * T * log (q * T)`,
and the square root of that is at most the sum of the two square root terms times the
square root of the log factor. -/
theorem gaussian_moment_sum_bound_F1606 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    sqrt (gaussianMomentSum χ δ T) ≤
      (sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T) * sqrt (log (q * T)) := by
  have h1 := leaf_gaussian_moment_sum_le q χ hχ δ T hT hzeros
  have h2 := leaf_sqrt_add_le Sec45.nTwo Sec45.nLog leaf_nTwo_nonneg leaf_nLog_nonneg
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hqT : (1 : ℝ) ≤ (q : ℝ) * T := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      have hqpos : 0 < q := NeZero.pos q
      have : (1 : ℕ) ≤ q := hqpos
      exact_mod_cast this
    nlinarith
  have hlog : 0 ≤ log ((q : ℝ) * T) :=
    Real.log_nonneg (by exact_mod_cast hqT)
  have hsum_nonneg : 0 ≤ Sec45.nTwo + Sec45.nLog :=
    add_nonneg leaf_nTwo_nonneg leaf_nLog_nonneg
  calc sqrt (gaussianMomentSum χ δ T)
      ≤ sqrt ((Sec45.nTwo + Sec45.nLog) * T * log (q * T)) := Real.sqrt_le_sqrt h1
    _ = sqrt ((Sec45.nTwo + Sec45.nLog) * (T * log (q * T))) := by ring_nf
    _ = sqrt (Sec45.nTwo + Sec45.nLog) * sqrt (T * log (q * T)) :=
        Real.sqrt_mul hsum_nonneg _
    _ = sqrt (Sec45.nTwo + Sec45.nLog) * (sqrt T * sqrt (log (q * T))) := by
        rw [Real.sqrt_mul hT0 _]
    _ ≤ (sqrt Sec45.nTwo + sqrt Sec45.nLog) * (sqrt T * sqrt (log (q * T))) := by
        gcongr
    _ = (sqrt Sec45.nTwo * sqrt T + sqrt Sec45.nLog * sqrt T) * sqrt (log (q * T)) := by ring_nf

end LeanLab.HelfgottMajor.DecompF1606
