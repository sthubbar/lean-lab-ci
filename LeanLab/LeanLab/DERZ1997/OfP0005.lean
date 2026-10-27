/-
P0011 Deshouillers, Effinger, te Riele, Zinoviev 1997: the even Goldbach input `dtr`,
`EvenGoldbachUpTo (10 ^ 13)`, discharged from P0005, Oliveira e Silva, Herzog, Pardi 2014,
taken as the hypothesis `EvenGoldbachUpTo (4 * 10 ^ 18)`, the same statement as the cited
`LeanLab.Verifications.oesilva_even`, verified faithful to the paper in unit U-7300.

Both ranges use the one lab definition `EvenGoldbachUpTo N`: every even `n` with `4 ≤ n ≤ N`
is `p + q` with `p, q` prime, the prime 2 allowed. No bridge between definitions is needed;
only `10 ^ 13 ≤ 4 * 10 ^ 18` and `1615 * 10 ^ 9 ≤ 4 * 10 ^ 18`.

`derz_main_of_P0005`: GRH implies ternary Goldbach, CONDITIONAL ON Zinoviev's `10^20` bound,
the paper's intermediate lemma, and P0005. The `sorry` theorems of Statements.lean are not used.

AI-written Lean code, Claude, 2026-10-21, run MANUAL-N3, unit U-7304. Checked only by the
Lean kernel. Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.DERZ1997.Statements

namespace LeanLab.DERZ1997.OfP0005
open LeanLab LeanLab.DERZ1997

/-- P0005 gives the paper's `dtr` range `10^13`. -/
theorem dtr_of_P0005 (hP0005 : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    EvenGoldbachUpTo (10 ^ 13) :=
  dtr_of hP0005 (by norm_num)

/-- P0005 gives the lowered range `1.615 · 10^12` that the printed lemma's gap needs. -/
theorem even1615_of_P0005 (hP0005 : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    EvenGoldbachUpTo (1615 * 10 ^ 9) :=
  fun n he h4 hn => hP0005 n he h4 (hn.trans (by norm_num))

/-- P0005 gives the range `1.545 · 10^12` of `EvenRange.derz_main_of_hsw_even`. -/
theorem even1545_of_P0005 (hP0005 : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    EvenGoldbachUpTo (1545 * 10 ^ 9) :=
  fun n he h4 hn => hP0005 n he h4 (hn.trans (by norm_num))

/-- **P0011 main theorem, CONDITIONAL ON P0005**: assuming GRH, every odd `n ≥ 7` is a sum of
three primes, from Zinoviev's `10^20` bound, the paper's lemma with gap `1.615 · 10^12`, and
P0005 in place of the Deshouillers-te Riele check `dtr`. -/
theorem derz_main_of_P0005
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hL : GRH → ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 →
      ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9)
    (hP0005 : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    GRH → TernaryGoldbach :=
  derz_main_of hZ hL (dtr_of_P0005 hP0005)

#print axioms dtr_of_P0005
#print axioms even1615_of_P0005
#print axioms even1545_of_P0005
#print axioms derz_main_of_P0005

end LeanLab.DERZ1997.OfP0005
