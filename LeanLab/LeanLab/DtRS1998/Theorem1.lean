/-
P0037 Deshouillers, te Riele, Saouter 1998, Theorem 1, p. 206 of the paper, page 3 of
papers/P0037.pdf: "We have G2 ≥ 10^14". G2 is defined on p. 205, page 2 of the PDF, as the least
upper bound of the G such that every even n with 4 ≤ n ≤ G is a sum of two primes.

`G2AtLeast N` is the faithful reading of G2 ≥ N for a natural N: every even n with 4 ≤ n < N is
a sum of two primes. A supremum can equal N while N itself fails, so the endpoint is excluded.
`EvenGoldbachUpTo N`, the lab's older encoding in Verifications.Statements.dtrs, includes the
endpoint and is slightly stronger; `g2AtLeast_of_upTo` gives the faithful form from it.

The paper's computation is not redone. `theorem1_of_P0005` is CONDITIONAL ON P0005,
Oliveira e Silva, Herzog, Pardi 2014, taken as the hypothesis EvenGoldbachUpTo (4 * 10^18),
the same statement as the cited `Verifications.oesilva_even`. No sorry is used here.

AI-written Lean code, Claude, 2026-10-21, run MANUAL-N3, unit U-7302. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Common.Goldbach

namespace LeanLab.DtRS1998.Theorem1

open LeanLab

/-- G2 ≥ N in the paper's sense, p. 205: every even `n` with `4 ≤ n < N` is a sum of two primes. -/
def G2AtLeast (N : ℕ) : Prop :=
  ∀ n, Even n → 4 ≤ n → n < N → IsGoldbachSum n

theorem g2AtLeast_of_upTo {N : ℕ} (h : EvenGoldbachUpTo N) : G2AtLeast N :=
  fun n he h4 hn => h n he h4 hn.le

theorem upTo_mono {M N : ℕ} (h : EvenGoldbachUpTo N) (hMN : M ≤ N) : EvenGoldbachUpTo M :=
  fun n he h4 hn => h n he h4 (hn.trans hMN)

/-- CONDITIONAL ON P0005: Theorem 1 of P0037 in the lab's endpoint-inclusive form. -/
theorem theorem1_upTo_of_P0005 (hP0005 : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    EvenGoldbachUpTo (10 ^ 14) :=
  upTo_mono hP0005 (by norm_num)

/-- CONDITIONAL ON P0005: Theorem 1 of P0037, G2 ≥ 10^14, in the faithful form. -/
theorem theorem1_of_P0005 (hP0005 : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    G2AtLeast (10 ^ 14) :=
  g2AtLeast_of_upTo (theorem1_upTo_of_P0005 hP0005)

/-- Non-vacuity of the conclusion's shape: the first instances hold outright. -/
theorem g2AtLeast_10 : G2AtLeast 10 := by
  intro n he h4 hn
  obtain ⟨k, rfl⟩ := he
  have hk1 : 2 ≤ k := by omega
  have hk2 : k ≤ 4 := by omega
  interval_cases k
  · exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  · exact ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩
  · exact ⟨3, 5, Nat.prime_three, Nat.prime_five, rfl⟩

#print axioms g2AtLeast_of_upTo
#print axioms theorem1_upTo_of_P0005
#print axioms theorem1_of_P0005
#print axioms g2AtLeast_10

end LeanLab.DtRS1998.Theorem1
