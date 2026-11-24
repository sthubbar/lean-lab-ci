/-
P0013 pages 70 and 71, the second Type I bound with corrected 3.49, split into leaves.
The original statement is Decomp119.typeI₂_bound; this file imports Decomp119,
so the assembly is stated here as typeI₂_bound_of_leaves.
The re-approximation leaf is shared with Decomp119LeavesII.reapprox.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119LeavesII

namespace LeanLab.HelfgottArcs.Decomp119LeavesI2
open LeanLab.HelfgottArcs.Decomp119

/-- LEAF: Lemma 3.7 in the case |δ'| ≤ 1/(2c_2), c_2 = 6π/(5√c_0), c_0 = 31.521: the
corrected bound for 3.49 plus the bound 1177.64 for 5.58 from 3.50. Class HARD.
P0013 pages 70 and 71, displays 3.49 and 5.58, with the 3.49 coefficient of
MinorSI2.firstLine_eq. -/
theorem lemma37_small_delta (x α : ℝ) (hx : 2.16e20 ≤ x) (a' : ℤ) (q' : ℕ) (δ' : ℝ)
    (hq1 : 1 ≤ q') (h2α : 2 * α = a' / q' + δ' / x) (hg : Int.gcd a' q' = 1)
    (hqQ : (q' : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hc : x ^ ((1 : ℝ) / 3) / 6 / 4 < q' ∨
        (8 < |δ'| ∧ 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q'))
    (hsmall : |δ'| ≤ 1 / (2 * (6 * Real.pi / (5 * Real.sqrt 31.521)))) :
    ‖I₂ α x‖ ≤ 3 * x ^ ((2 : ℝ) / 3) * (2 / 3 * Real.log x - Real.log 18) +
      0.02017 * (x ^ ((2 : ℝ) / 3) * Real.log x) +
      (1177.64 * (x ^ ((2 : ℝ) / 3) * Real.log x) +
        0.0006406 * (x ^ ((2 : ℝ) / 3) * Real.log x ^ 2)) := by
  sorry

/-- LEAF: Lemma 3.7 in the case |δ'| > 1/(2c_2): the corrected bound for 3.49 plus the
bound for 3.51 with ε = 0.01 before its coarse rounding. Class HARD. P0013 pages 70
and 71, display 3.49 and the display ending 1212.591 x^{2/3} log x + 29.131 x^{1/2} log x. -/
theorem lemma37_large_delta (x α : ℝ) (hx : 2.16e20 ≤ x) (a' : ℤ) (q' : ℕ) (δ' : ℝ)
    (hq1 : 1 ≤ q') (h2α : 2 * α = a' / q' + δ' / x) (hg : Int.gcd a' q' = 1)
    (hqQ : (q' : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hc : x ^ ((1 : ℝ) / 3) / 6 / 4 < q' ∨
        (8 < |δ'| ∧ 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q'))
    (hlarge : 1 / (2 * (6 * Real.pi / (5 * Real.sqrt 31.521))) < |δ'|) :
    ‖I₂ α x‖ ≤ 3 * x ^ ((2 : ℝ) / 3) * (2 / 3 * Real.log x - Real.log 18) +
      0.02017 * (x ^ ((2 : ℝ) / 3) * Real.log x) +
      (1212.591 * (x ^ ((2 : ℝ) / 3) * Real.log x) + 29.131 * Real.sqrt x * Real.log x) := by
  sorry

/-- Assembly of Decomp119.typeI₂_bound from the re-approximation leaf and the two
case leaves, exact parent statement. -/
theorem typeI₂_bound_of_leaves (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ‖I₂ α x‖ ≤ typeI₂Budget x := by
  obtain ⟨a', q', δ', hq1, h2α, hg, hqQ, hδ, hc⟩ :=
    Decomp119LeavesII.reapprox x α a q δ h hq
  have hx : 2.16e20 ≤ x := h.1
  unfold typeI₂Budget
  by_cases hs : |δ'| ≤ 1 / (2 * (6 * Real.pi / (5 * Real.sqrt 31.521)))
  · have h1 := lemma37_small_delta x α hx a' q' δ' hq1 h2α hg hqQ hδ hc hs
    have hm := le_max_left (1177.64 * (x ^ ((2 : ℝ) / 3) * Real.log x) +
        0.0006406 * (x ^ ((2 : ℝ) / 3) * Real.log x ^ 2))
      (1212.591 * (x ^ ((2 : ℝ) / 3) * Real.log x) + 29.131 * Real.sqrt x * Real.log x)
    simp only
    linarith
  · have h1 := lemma37_large_delta x α hx a' q' δ' hq1 h2α hg hqQ hδ hc (lt_of_not_ge hs)
    have hm := le_max_right (1177.64 * (x ^ ((2 : ℝ) / 3) * Real.log x) +
        0.0006406 * (x ^ ((2 : ℝ) / 3) * Real.log x ^ 2))
      (1212.591 * (x ^ ((2 : ℝ) / 3) * Real.log x) + 29.131 * Real.sqrt x * Real.log x)
    simp only
    linarith

end LeanLab.HelfgottArcs.Decomp119LeavesI2
