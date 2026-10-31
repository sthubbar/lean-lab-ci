/-
P0059 arXiv 1407.7902v1 page 12 equation 3.9.
An elementary enclosure test for the printed c0 expression.
The application to the printed coefficients remains a QUESTION for review.
AI wrote this Lean code, CODEX task92, 2026-10-26.
-/
import Mathlib

namespace LeanLab.KadiriLumley2014.Task92
open Real

/-- The printed c0 expression is below 0.7508 under coarse coefficient
bounds containing the displayed values. This is a parameter implication,
not a proof about the external zero estimates. -/
theorem printed_c0_enclosure_bound {w1 w2 w3 v1 v3 v4 v5 L t : ℝ}
    (hw1 : w1 ≤ 0.08) (hw2 : w2 ≤ 0) (hw3 : w3 ≤ 0)
    (hv1 : 0.15 ≤ v1) (hv3 : 0 ≤ v3) (hv4 : 0 ≤ v4) (hv5 : 0 ≤ v5)
    (hL : 1 ≤ L) (ht : 0 < t) :
    (w1 + w2 / L + w3 / L ^ 2) /
      (v1 + v3 / t + v4 * Real.log L / (t * L) + v5 / (t * L)) < 0.7508 := by
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have h2 : w2 / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg hw2 hL0.le
  have h3 : w3 / L ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hw3 (sq_nonneg L)
  have hn : w1 + w2 / L + w3 / L ^ 2 ≤ 0.08 := by linarith
  have hd : 0.15 ≤ v1 + v3 / t + v4 * Real.log L / (t * L) + v5 / (t * L) := by
    have h31 : 0 ≤ v3 / t := div_nonneg hv3 ht.le
    have h41 : 0 ≤ v4 * Real.log L / (t * L) := by positivity
    have h51 : 0 ≤ v5 / (t * L) := by positivity
    linarith
  apply (div_lt_iff₀ (by linarith : 0 < v1 + v3 / t + v4 * Real.log L / (t * L) + v5 / (t * L))).mpr
  nlinarith

end LeanLab.KadiriLumley2014.Task92
