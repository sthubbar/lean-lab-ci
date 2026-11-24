/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 9 Theorem 2.7 display 2.64 and
page 13 Table 2. SPLIT of Task92.table_endpoint_budget from Decomp92.lean,
ROUTE BURST S98 burst-20261122.
The split follows the falsifier note notes/burst-20261115/KadiriLumley2014-falsifier-table2.md.
The paper envelope of Lemma 2.6 with the corrected S5 of display 2.44 does not close any
row, so the leaves follow the route that evaluates the zero sum itself below the verified
height H = 3.061e10 by input d of Theorem 3.2, and bounds the zeros above H by the
corrected B3, B41 and B42. That route is numerically positive on the sixteen rows
log 4e18 and 43 to 57, at least 0.0107 at this endpoint, and negative on rows 58, 59, 60
and 150, which hold only under RH above H, with margins 0.018 to 0.045.
So the rows are split in two leaves of different strength.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.Decomp92

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- LEAF: page 9 Theorem 2.7 display 2.64 at the row endpoint, for the sixteen Table 2 rows
on page 13 with log index at most 57, that is log 4e18 and 43 to 57. Route: display 2.20,
the zero sum over zeros of height at most H = 3.061e10 bounded by partial summation
against the Riemann von Mangoldt count with Rosser's error, input d of Theorem 3.2 on
page 11, and the zeros above H bounded by B3, B42 and B41 of pages 7 to 9 with S5 of
display 2.44 corrected to R0 over log X0 as in the Faber and Kadiri corrigendum.
Uncertified mpmath margin at this endpoint 0.0107 to 0.2748.
Class HARD. -/
theorem table_endpoint_budget_low {r : PrintedRow} (hr : r ∈ tableTwo)
    (hlow : r.logIndex ≤ 57) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  sorry

/-- LEAF: page 9 Theorem 2.7 display 2.64 at the row endpoint, for the four Table 2 rows on
page 13 with log index 58, 59, 60 and 150. QUESTION: with the zero density input d of
Theorem 3.2 at H = 3.061e10 and the corrected S5 of display 2.44 the route margin is
negative, -0.0032, -0.0158, -0.0202 and -0.0234, while with all zeros above H on the
critical line it is positive, 0.018 to 0.045. Closing this leaf needs a larger verified
height, for example Platt and Trudgian 3e12, with matching density constants, or
re-optimised row parameters. Not suspected false.
Class HARD. -/
theorem table_endpoint_budget_high {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  sorry

theorem table_endpoint_budget_split {r : PrintedRow} (hr : r ∈ tableTwo) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  by_cases h : r.logIndex ≤ 57
  · exact table_endpoint_budget_low hr h
  · exact table_endpoint_budget_high hr (by omega)

end LeanLab.KadiriLumley2014.Task92
