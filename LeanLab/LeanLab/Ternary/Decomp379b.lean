/-
Helfgott https://arxiv.org/abs/1312.7748v2, pages 56 and 69 to 71.
Use the corrected minor arc arithmetic already proved in Helfgott2013.Slip.
The weighted total and the discarded part are separate analytic inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.State1535
import LeanLab.HelfgottArcs.Statements
import LeanLab.Helfgott2013.Slip

namespace LeanLab.Ternary.Task379
open Finset
open scoped ArithmeticFunction

/-- A finite ordered triple sum with arbitrary real weights.
Helfgott page 70, equation 7.49. Terms outside the sum constraint vanish.
Nonnegative integer triples with sum N already have every coordinate at most N. -/
noncomputable def weightedTotal (N : ℕ) (w : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1), ∑ r ∈ range (N + 1),
    if p + q + r = N then w p q r else 0

/-- The discarded terms with an even or nonprime coordinate.
Helfgott page 70, equation 7.50, with arbitrary real weights. -/
noncomputable def discardedTotal (N : ℕ) (w : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1), ∑ r ∈ range (N + 1),
    if p + q + r = N ∧ ¬ (p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧ r.Prime ∧ Odd r)
      then w p q r else 0

/-- The actual scaled weights used in Helfgott section 7, page 56.
Eta plus has H equal to 200. Eta star is the Mellin convolution at scale 49.
The von Mangoldt factors are retained before the discarded terms are removed. -/
noncomputable def helfgottTripleWeight (N p q r : ℕ) : ℝ :=
  let x := LeanLab.Helfgott2013.xOf N
  (Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ) *
    LeanLab.HelfgottArcs.etaPlus (p / x) * LeanLab.HelfgottArcs.etaPlus (q / x) *
    LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
      (49 * (r / x))

/-- A positive gap after discarding terms contains a prime triple.
Helfgott page 70, final positivity argument. No weight sign condition is needed. -/
theorem isTernarySum_of_weighted_gap {N : ℕ} {w : ℕ → ℕ → ℕ → ℝ}
    (h : 0 < weightedTotal N w - discardedTotal N w) : IsTernarySum N := by
  classical
  by_contra hN
  have he : weightedTotal N w = discardedTotal N w := by
    unfold weightedTotal discardedTotal
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro r hr
    by_cases hs : p + q + r = N
    · have hn : ¬ (p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧ r.Prime ∧ Odd r) := by
        intro hh
        exact hN ⟨p, q, r, hh.1, hh.2.2.1, hh.2.2.2.2.1, hs⟩
      simp only [hs, hn, not_false_eq_true, and_self, ite_true]
    · simp only [hs, false_and, ite_false]
  rw [he, sub_self] at h
  exact lt_irrefl 0 h

/-- LEAF. The major and minor arc analysis lower bounds the full weighted count.
Helfgott pages 62 and 69 to 70, equations 7.25, 7.48 and 7.49.
Use the repaired minor coefficient 0.97757 from the existing Slip proof,
so the total coefficient is the weaker valid 0.08068 rather than printed 0.08433.
This leaf counts prime powers as well as primes and has no representation conclusion. -/
theorem helfgott_weighted_total_lower (N : ℕ) (ho : Odd N)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    0.08068 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ ≤
      weightedTotal N (helfgottTripleWeight N) := by sorry

/-- LEAF. The even and nonprime contribution is bounded separately.
Helfgott page 70, equation 7.50 and the following RS62 estimates.
The coefficients use the actual smoothing weights, before any existence argument. -/
theorem helfgott_discarded_upper (N : ℕ)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    discardedTotal N (helfgottTripleWeight N) ≤
      7.3306 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.log N := by sorry

/-- The exact sealed Helfgott analytic threshold from two smaller estimates.
Helfgott page 70, final display, with the corrected coefficient proved in Slip.
CONDITIONAL ON helfgott_weighted_total_lower and helfgott_discarded_upper. -/
theorem helfgott_analytic_decomposed : TernaryAbove (10 ^ 27) := by
  intro N ho hN
  have hN' : (1e27 : ℝ) ≤ N := by convert hN using 1 <;> norm_num
  have hgap := (LeanLab.Helfgott2013.repaired_chain hN'
    (helfgott_weighted_total_lower N ho hN) (helfgott_discarded_upper N hN)).2.2
  exact isTernarySum_of_weighted_gap hgap

/-- The exact sealed weighted Chen and Wang statement follows through the threshold chain.
P0033 page 169, main theorem, using the proved threshold comparisons in this folder.
This is a derived bridge from Helfgott, not a formalization of the 1996 argument.
CONDITIONAL ON the two explicit Helfgott estimates above. -/
theorem chenWang_weighted_decomposed :
    LeanLab.Ternary.U1535.ChenWangWeighted (Real.exp (Real.exp 9.715)) :=
  LeanLab.Ternary.U1535.chenWangWeighted_of_ternaryAbove
    (chenWang_of_liuWang (liuWang_of_helfgott helfgott_analytic_decomposed))

end LeanLab.Ternary.Task379
