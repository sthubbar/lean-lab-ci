/-
Split of the singular series tail `singular_tail357` into three steps, with one
further ingredient supporting the third step. Nothing here changes the
statement: `singular_tail357_split` states it character for character and proves
it from the leaves below, which record, in order, (1) the Euler product identity
for the full Ramanujan weight series, (2) the finite Ramanujan sum up to N to the
one tenth against the product of the local factors at the primes up to that
point, and (3) that finite product against the full series, whose size is
controlled by (4) the tail of the reciprocal squares of p minus one.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357l

namespace LeanLab.Linnik1951

open Finset
open scoped Topology BigOperators

/-- LEAF. Step 1 of 3: the Euler product identity. The weight sending q to the
square of the Moebius function at q over the square of the totient of q, times
the real part of the Ramanujan sum of q at n, is multiplicative across coprime
moduli and is supported on squarefree q, so the series over all q converges and
its sum is the Euler product over the primes that defines the singular series.
This is the identity alone: it carries no truncation, no rate and no uniformity
in N. -/
theorem singular_series_has_sum357 (n : ℕ) (hn : 2 ≤ n) :
    HasSum (fun q : ℕ =>
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (singularSeries111 n) := by
  sorry

/-- LEAF. Step 2 of 3: the truncated sum against the finite product of local
factors. The finite Ramanujan sum over the moduli from one to N to the one tenth
differs from the product over the primes up to N to the one tenth of the local
factor 1 plus 1 over p minus 1 at a prime dividing n and 1 minus the inverse
square of p minus 1 at a prime not dividing n, by at most an absolute constant
times N to the minus one hundredth. The content is the divisor expansion of the
Ramanujan sum, which makes the squarefree weight multiplicative, together with
the bound on the squarefree moduli beyond the cut off. The saving one hundredth
is far weaker than the one tenth power of the cut off that the argument leaves
free. -/
theorem truncated_sum_euler_error357 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n -
          (∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
            (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2))| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  sorry

/-- LEAF. Step 3 of 3: the finite product against the full series. The product
over the primes up to N to the one tenth of the same local factors differs from
the sum of the full Ramanujan weight series by at most an absolute constant
times N to the minus one hundredth. The content is that every local factor is at
most 1 plus the reciprocal square of p minus 1, so the product over the primes
beyond the cut off differs from one by at most the tail of those reciprocal
squares, which is the fourth leaf below. -/
theorem prime_product_series_tail357 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |(∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
            (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) -
          (∑' q : ℕ, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  sorry

/-- LEAF. Ingredient of step 3: the prime reciprocal square tail. Beyond some
point the sum of the reciprocal squares of p minus 1 over the primes larger than
N to the one tenth is at most twice the reciprocal of the integer cut off. This
is an elementary estimate on primes alone: it names no singular series, no
Ramanujan sum and no even integer, and it is the only place where the cut off is
compared with a convergent prime series. -/
theorem prime_reciprocal_square_tail357 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      (∑' p : Nat.Primes,
        if ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ < (p : ℕ) then
          1 / (((p : ℕ) : ℝ) - 1) ^ 2 else 0) ≤
        2 / ((⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ)) := by
  sorry

/-- Assembly of `singular_tail357` from the leaves above: write the singular
series as the sum of the full Ramanujan weight series through step 1, insert the
finite product of local factors as an intermediate term, and bound the two
halves by step 2 and step 3, with the two constants added. No step uses
`singular_tail357` itself. -/
theorem singular_tail357_split :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n - singularSeries111 n| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  obtain ⟨C1, hC1, N1, h1⟩ := truncated_sum_euler_error357
  obtain ⟨C2, hC2, N2, h2⟩ := prime_product_series_tail357
  refine ⟨C1 + C2, by positivity, max N1 N2, ?_⟩
  intro N hN n hn2 hnN hev
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos_nat : 0 < N := lt_of_le_of_lt (Nat.zero_le N1) hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hx : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) := (Real.rpow_pos_of_pos hNpos _).le
  have hb1 := h1 N hN1 n hn2 hnN hev
  have hb2 := h2 N hN2 n hn2 hnN hev
  have hsum := singular_series_has_sum357 n hn2
  have htsum : (∑' q : ℕ,
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) = singularSeries111 n :=
    hsum.tsum_eq
  rw [← htsum]
  calc
    |truncatedSingular357 N n -
        (∑' q : ℕ, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)|
        = |(truncatedSingular357 N n -
            (∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
              (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2))) +
            ((∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
              (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) -
              (∑' q : ℕ, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
                (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re))| := by
          congr 1
          ring
    _ ≤ |truncatedSingular357 N n -
            (∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
              (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2))| +
          |(∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
              (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) -
            (∑' q : ℕ, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
              (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)| :=
        abs_add_le _ _
    _ ≤ C1 * (N : ℝ) ^ (-(1 / 100 : ℝ)) + C2 * (N : ℝ) ^ (-(1 / 100 : ℝ)) :=
        add_le_add hb1 hb2
    _ = (C1 + C2) * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
        ring

end LeanLab.Linnik1951
