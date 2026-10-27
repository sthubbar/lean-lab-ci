/-
Helfgott and Platt 2013, P0006, unit U-6816, run 20261021T0316Z-cloud57.
Theorem 4.1 with its binary input filled by the lab's cited P0005 statement
`LeanLab.Verifications.oesilva_even`, Oliveira e Silva, Herzog and Pardi 2014, a `sorry`
standing for their computation. So `#print axioms` here shows `sorryAx`: this is CITED, not
PROVED. What remains as a hypothesis is only the paper's own computation, the 492,700 range
ladders of Section 4, or for the top segment a lower ternary range.
AI-written Lean code, Claude, 2026-10-21. Ternary Goldbach is Helfgott's theorem; binary
Goldbach is OPEN.
-/
import LeanLab.HelfgottPlatt.HelfgottPlattU6816Sharp
import LeanLab.HelfgottPlatt.HelfgottPlattU6816Top
import LeanLab.Verifications.Statements

namespace LeanLab.HelfgottPlatt.U6816.Cited

open LeanLab.HelfgottPlatt.Proth LeanLab.HelfgottPlatt.U6816

/-- Theorem 4.1 from the cited P0005 input and the paper's range ladders. CITED. -/
theorem theorem4_1_cited (L : ℕ → List ℕ) (hL : ∀ i < 492700, RangeOK i (L i)) :
    TernaryGoldbachUpTo T :=
  theorem4_1_of_ranges LeanLab.Verifications.oesilva_even L hL

/-- The kernel-checked top segment from the cited P0005 input. CITED. -/
theorem top_segment_cited (hA : TernaryGoldbachUpTo (8875694143621751943882526949377 + 2)) :
    TernaryGoldbachUpTo T :=
  Top.top_segment LeanLab.Verifications.oesilva_even hA

end LeanLab.HelfgottPlatt.U6816.Cited
