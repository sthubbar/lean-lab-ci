/-
P0013 pages 71 and 72, the Type II bound 5.60 and its two smaller cases, split into leaves.
The original statement is Decomp119.typeII_bound; this file imports Decomp119,
so the assembly is stated here as typeII_bound_of_leaves.
The paper uses a new approximation 2α = a'/q' + δ'/x with q' ≤ Q = x^{2/3}/(500√6)
and |δ'/x| ≤ 1/(q'Q); the leaves keep that re-approximation explicit.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119

namespace LeanLab.HelfgottArcs.Decomp119LeavesII
open LeanLab.HelfgottArcs.Decomp119

/-- LEAF: page 70, the new approximation for the second choice of parameters: Dirichlet
with Q = x/U, and either case a, q' > y/4, or case b, |δ'| > 8 and |δ'|q' > 8y.
Class HARD. P0013 page 70, the paragraph after the choice of V, U, Q and page 71 line
"either (a) q > y/4, or both (b1) and (b2)"; here y = x^{1/3}/6. -/
theorem reapprox (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ∃ a' : ℤ, ∃ q' : ℕ, ∃ δ' : ℝ, 1 ≤ q' ∧ 2 * α = a' / q' + δ' / x ∧ Int.gcd a' q' = 1 ∧
      (q' : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6) ∧
      |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))) ∧
      (x ^ ((1 : ℝ) / 3) / 6 / 4 < q' ∨
        (8 < |δ'| ∧ 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')) := by
  sorry

/-- LEAF: page 71 display 5.59 from 5.33, maximized at q' = y and evaluated at
x_0 = 2.16e20, giving 5.60 for y/4 < q' ≤ x/(2e^2 U). Class HARD. P0013 pages 71
and 72, displays 5.59 and 5.60. -/
theorem caseA_small (x α : ℝ) (hx : 2.16e20 ≤ x) (a' : ℤ) (q' : ℕ) (δ' : ℝ)
    (h2α : 2 * α = a' / q' + δ' / x) (hg : Int.gcd a' q' = 1)
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hlo : x ^ ((1 : ℝ) / 3) / 6 / 4 < q')
    (hhi : (q' : ℝ) ≤ x / (2 * Real.exp 2 * U x)) :
    ‖II α x‖ ≤ 0.272652 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: page 72, the range x/(2e^2 U) < q' ≤ Q treated with 5.34, giving
0.10198 x^{5/6} (log x)^{3/2}. Class HARD. P0013 page 72, the display after 5.60. -/
theorem caseA_large (x α : ℝ) (hx : 2.16e20 ≤ x) (a' : ℤ) (q' : ℕ) (δ' : ℝ)
    (h2α : 2 * α = a' / q' + δ' / x) (hg : Int.gcd a' q' = 1)
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hlo : x / (2 * Real.exp 2 * U x) < q')
    (hhi : (q' : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6)) :
    ‖II α x‖ ≤ 0.10198 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- LEAF: page 72, case b with q' ≤ y treated with 5.36, giving
0.24956 x^{5/6} (log x)^{3/2}. Class HARD. P0013 page 72, the display for case b. -/
theorem caseB (x α : ℝ) (hx : 2.16e20 ≤ x) (a' : ℤ) (q' : ℕ) (δ' : ℝ)
    (h2α : 2 * α = a' / q' + δ' / x) (hg : Int.gcd a' q' = 1) (hq1 : 1 ≤ q')
    (hδ : |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))))
    (hb1 : 8 < |δ'|) (hb2 : 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')
    (hy : (q' : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6) :
    ‖II α x‖ ≤ 0.24956 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  sorry

/-- Assembly of Decomp119.typeII_bound from the four leaves, exact parent statement:
5.60 is the worst of the three cases, page 72. -/
theorem typeII_bound_of_leaves (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ‖II α x‖ ≤ 0.272652 * x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) := by
  obtain ⟨a', q', δ', hq1, h2α, hg, hqQ, hδ, hc⟩ := reapprox x α a q δ h hq
  have hx : 2.16e20 ≤ x := h.1
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hW : 0 ≤ x ^ ((5 : ℝ) / 6) * Real.log x ^ ((3 : ℝ) / 2) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
  rcases hc with ha | ⟨hb1, hb2⟩
  · by_cases hs : (q' : ℝ) ≤ x / (2 * Real.exp 2 * U x)
    · exact caseA_small x α hx a' q' δ' h2α hg hδ ha hs
    · have := caseA_large x α hx a' q' δ' h2α hg hδ (lt_of_not_ge hs) hqQ
      nlinarith
  · by_cases hy : (q' : ℝ) ≤ x ^ ((1 : ℝ) / 3) / 6
    · have := caseB x α hx a' q' δ' h2α hg hq1 hδ hb1 hb2 hy
      nlinarith
    · rw [not_le] at hy
      have hy4 : x ^ ((1 : ℝ) / 3) / 6 / 4 < q' := by
        have : 0 ≤ x ^ ((1 : ℝ) / 3) / 6 := by positivity
        linarith
      by_cases hs : (q' : ℝ) ≤ x / (2 * Real.exp 2 * U x)
      · exact caseA_small x α hx a' q' δ' h2α hg hδ hy4 hs
      · have := caseA_large x α hx a' q' δ' h2α hg hδ (lt_of_not_ge hs) hqQ
        nlinarith

end LeanLab.HelfgottArcs.Decomp119LeavesII
