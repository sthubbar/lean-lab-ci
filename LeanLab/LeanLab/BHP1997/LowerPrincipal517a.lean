/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
The open analytic leaves behind `LowerShortC165.lower_principal_density`, one for each
rough term of the raw coefficient and one for the lab normalization factor.
No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.LowerPrincipal517g
import LeanLab.BHP1997.DensitySlope517b

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 page 51, display 5.17, the E2 term. "A straightforward consequence of the
prime number theorem" applied to the sum over `p1 p2 n3 = m` with exponents in E2: the prime
number theorem with error term for `p1`, `p2` and each prime factor of the rough `n3`, with the
Buchstab identity, gives the local density `(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) /
(β1 β2^2)` at `m = Z^s`, with every log power saved on every prefix of J. -/
theorem leaf_two_rough_density (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  exact two_rough_density_of_leaves ω hω hz hε hε8

/-- P0069 page 51, display 5.17, the E4 term. The same consequence of the prime number
theorem for the sum over `p1 p2 p3 p4 n5 = m` with exponents in E4: the local density at
`m = Z^s` is the E4 integral with `1` replaced by `s`, over `log Z`, with every log power
saved on every prefix of J. -/
theorem leaf_four_rough_density (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  exact four_rough_density_of_leaves ω hω hz hε hε8

/-- P0069 page 51, "A computer calculation yields" with the U-1624 normalization of
pages 51 and 52. The density `V(s)` of the raw coefficient decreases through `s = 1` fast
enough that the factor `v0 log Z / (log Y * V(s))` needs no clipping on J: `v0 ≥ 0` and
`V(s) ≥ v0 (1 + 3 (1 - s))` just below `s = 1`. This is a lab normalization fact about the
page 51 integrals, not a printed formula; numerically `v0` is near 0.0637 and the slope of `V`
at one is near minus 2.09. -/
theorem leaf_density_slope (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    0 ≤ lowerV0 ω ε ∧ ∃ s0 : ℝ, s0 < 1 ∧ ∀ s : ℝ, s0 ≤ s → s ≤ 1 →
      lowerV0 ω ε * (1 + 3 * (1 - s)) ≤ lowerDensityAt ω ε s := by
  exact density_slope ω hω hz hε hε8

end LeanLab.BHP1997.LowerShortC165
