/-
P0069 Baker, Harman and Pintz 1997, Section 5, pages 51 and 52, display 5.17 and the lab
normalization of the density `V(s)` of the raw lower coefficient near `s = 1`.

`density_slope` has exactly the statement of `leaf_density_slope` of LowerPrincipal517a. It is
`density_slope_of_two_upper` of DensitySlope517 with its hypothesis, the certified page 51
bound `E2 integral ≤ 3799/4000`, supplied by the grid enclosure
`lower_two_integral_grid_bound` and the certificate total `lower_two_grid_total`, the same
three lines as `DecompC165d.lower_two_integral_bound`. CONDITIONAL on the two numeric leaves
`leaf_two_region_quadrature` and `leaf_two_variation_quadrature` of DensitySlope517.
No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DensitySlope517
import LeanLab.BHP1997.Certificate312Total

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

/-- P0069 pages 51 and 52, display 5.17 and the lab normalization of U-1624: the density `V(s)`
of the raw coefficient decreases through `s = 1` fast enough that the factor
`v0 log Z / (log Y * V(s))` needs no clipping on J: `v0 ≥ 0` and `V(s) ≥ v0 (1 + 3 (1 - s))`
for `s ∈ [99/100, 1]`. The statement is exactly that of `leaf_density_slope`. CONDITIONAL on
`leaf_two_region_quadrature` and `leaf_two_variation_quadrature`. -/
theorem density_slope (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    0 ≤ lowerV0 ω ε ∧ ∃ s0 : ℝ, s0 < 1 ∧ ∀ s : ℝ, s0 ≤ s → s ≤ 1 →
      lowerV0 ω ε * (1 + 3 * (1 - s)) ≤ lowerDensityAt ω ε s :=
  density_slope_of_two_upper ω hω hz hε hε8
    (two_upper_of_grid (lower_two_integral_grid_bound hω hz hε.le hε8) lower_two_grid_total)

end LeanLab.BHP1997.LowerShortC165
