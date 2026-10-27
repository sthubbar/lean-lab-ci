import LeanLab.GoldbachAverage.GSTheorem3Bound
import LeanLab.GoldbachAverage.ThetaGallagher

/-!
Concrete nonzero checks for the two coefficient normalizations used in task43.
P0051 arXiv 2110.14250v2 page 3 eq. 12 and page 4 eqs. 18 and 19.
The positive index error coefficients start with zero at index zero.
The weighted geometric comparison coefficients start with minus one.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage
open Finset Complex

/-- The actual error at N equals two is one, at every admissible radius. -/
theorem EGS_two (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : EGS 2 r = 1 := by
  have h1 : dc 1 = 0 := by
    rw [dc_eq_real]
    norm_num [cfr, sum_range_succ]
  have h2 : dc 2 = 1 := by
    rw [dc_eq_real]
    norm_num [cfr, sum_range_succ]
  have hs : Icc 1 2 = ({1, 2} : Finset ℕ) := by
    ext n
    simp only [mem_Icc, mem_insert, mem_singleton]
    omega
  rw [EGS_eq 2 hr0 hr1, hs]
  norm_num [h1, h2]

/-- A nonzero concrete majorant instance, not a zero integral. -/
theorem Emajorant_two_ge_one (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    1 ≤ Emajorant 2 r := by
  have h := norm_EGS_le_Emajorant 2 r
  rw [EGS_two r hr0 hr1, norm_one] at h
  exact h

/-- The weighted window includes minus one at index zero. -/
theorem weighted_window_at_two :
    LeanLab.PNTPort.Gallagher.win (ThetaLayers.weightedCoeff 2) 1 1 0 = -1 := by
  norm_num [LeanLab.PNTPort.Gallagher.win, ThetaLayers.weightedCoeff,
    LeanLab.PNTPort.Gallagher.lam1]

end LeanLab.GoldbachAverage
