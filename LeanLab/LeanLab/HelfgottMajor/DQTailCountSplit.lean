import LeanLab.HelfgottMajor.TailIntegral123
import LeanLab.HelfgottMajor.MainHyps123
import LeanLab.HelfgottMajor.DQTailIBPBranches

/-!
Split of `DQTailUnpaired.two_sided_envelope_count_le`, burst-20261124 S1, tag dq_count_split.
P0014, Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Lemma 4.5, page 41,
displays 4.33 to 4.35, with the Stieltjes summation after display 4.28 on page 38.

The counting step is cut at the one place where zeros stop mattering.
* `envelope_sum_le_stieltjes_count`, LEAF HARD: Stieltjes summation of the decreasing two
  branch envelope f against the two sided zero count N, followed by the pointwise count bound
  of `MainTail123.zero_count_two_sided_of_book`. The zero sum is at most the integral over t
  above T of minus f prime of t times 2 bookMain t plus 2 bookError t minus 2 bookMain T plus
  2 bookError T.
* `stieltjes_integral_le_tail`, proved from the two branch LEAFs of `DQTailIBPBranches`,
  formerly a LEAF MEDIUM: pure calculus, no zeros. Integration by parts
  turns that integral into the integral of f times twice the derivative of bookMain plus
  bookError, plus the boundary 4 f of T bookError of T, and the derivative is below twice
  `TailIntegral123.countDensity`.
The minus derivative of the envelope is written out: 0.1598 e to the minus 0.1598 t for the
exponential branch, and 0.213 t over pi delta squared times the Gaussian for the Gaussian
branch, since 2 times 0.1065 is 0.213. No new definitions.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.DQTailCountSplit
open Real LeanLab.HelfgottMajor

/-- LEAF: P0014 page 41, display 4.35, Stieltjes summation after display 4.28 on page 38,
with no pairing, then the two sided count of `MainTail123.zero_count_two_sided_of_book`.
Class HARD. CONDITIONAL ON hB, the book zero count of display 4.26 on page 38.
Route: f of abs gamma is the integral of minus f prime above abs gamma; Tonelli gives the
integral of minus f prime times N of t minus N of T; then bound N pointwise. -/
theorem envelope_sum_le_stieltjes_count (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) ≤
      ∫ t in Set.Ioi T,
        (0.1598 * exp (-0.1598 * t) +
          if δ = 0 then 0 else
            0.213 * t / (π * |δ|) ^ 2 * exp (-0.1065 * (t / (π * |δ|)) ^ 2)) *
        (2 * ZeroCount1623.bookMain q t + 2 * ZeroCount1623.bookError q t -
          2 * ZeroCount1623.bookMain q T + 2 * ZeroCount1623.bookError q T) := by
  sorry

/-- PROVED, CONDITIONAL ON the two branch LEAFs of `DQTailIBPBranches`, formerly LEAF MEDIUM.
P0014 page 41, displays 4.35 and 4.36, integration by parts on Ioi T keeping the
boundary term that page 38 drops. Pure real analysis, no zeros.
Route: the constant 4 bookError T part gives 4 bookError T times f of T; the rest gives the
integral of f times 1 over pi log of qt over 2 pi plus 0.3 over t, at most 2 countDensity. -/
theorem stieltjes_integral_le_tail
    (q : ℕ) [NeZero q] (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    (∫ t in Set.Ioi T,
        (0.1598 * exp (-0.1598 * t) +
          if δ = 0 then 0 else
            0.213 * t / (π * |δ|) ^ 2 * exp (-0.1065 * (t / (π * |δ|)) ^ 2)) *
        (2 * ZeroCount1623.bookMain q t + 2 * ZeroCount1623.bookError q t -
          2 * ZeroCount1623.bookMain q T + 2 * ZeroCount1623.bookError q T)) ≤
      2 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      4 * (exp (-0.1598 * |T|) +
        if δ = 0 then 0 else exp (-0.1065 * (|T| / (π * |δ|)) ^ 2)) *
        ZeroCount1623.bookError q T := by
  -- CONDITIONAL ON the two branch LEAFs of `DQTailIBPBranches`, burst-20261124 S1.
  have hT100 : (100 : ℝ) ≤ T := (le_max_right _ _).trans hT
  obtain ⟨hiE, hE⟩ := DQTailIBPBranches.exp_branch_ibp q T hT100
  by_cases hδ : δ = 0
  · have hG : TailIntegral123.gaussianTailIntegral (q : ℝ) δ T = 0 := by
      unfold TailIntegral123.gaussianTailIntegral; simp [hδ]
    simp only [hδ, ite_true, add_zero]
    rw [hδ] at hG
    rw [hG]
    linarith
  · obtain ⟨hiG, hG⟩ := DQTailIBPBranches.gaussian_branch_ibp q δ T hδ hT
    simp only [hδ, ite_false, add_mul]
    rw [MeasureTheory.integral_add hiE hiG]
    linarith

end LeanLab.HelfgottMajor.DQTailCountSplit

#print axioms LeanLab.HelfgottMajor.DQTailCountSplit.stieltjes_integral_le_tail
