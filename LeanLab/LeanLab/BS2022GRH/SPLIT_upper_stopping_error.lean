/-
Split of the OPEN target `upper_stopping_error` of Decomp327b, the signed upper stopping error
of BJS arXiv 2207.09452v6, Lemma 11 display 33 summed over odd n as in Proposition 13 p. 14,
with the constant C1 of Lemma 14 read from journal Table 1 p. 1218.

The target sums, over odd n, the stopping term T_n of display 28 minus V times the delay term f_n.
The paper proof bounds each term by V times epsilon tau_n e^2 h of s, display 32, and sums the
tau_n over odd n into C1 of epsilon, which Table 1 bounds by 112.

The n equal to one term is ALREADY PROVED in Decomp327a as `first_stopping_bound`, with tau_1
equal to 3, BJS p. 11. This file uses it, so the open content is the odd n at least 3 tail with
coefficient 112 minus 3, that is 109, which is exactly the sum of tau_{2n-1} over n at least 2.
That tail is split by the range of s into the piece where h is the constant e^{-2}, s at most 2,
and the piece where h of s is e^{-s}, s from 2 to 3, the two branches of BJS display 7.

This file adds no definition, changes no existing file, and leaves the sealed statement untouched.
The assembly declares neither the target nor any leaf as a hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.Decomp327b

namespace LeanLab.BS2022GRH.Decomp327b
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d Decomp327a
noncomputable section

/-- LEAF: BJS Lemma 11 for odd n at least 3, case n odd and 1 at most s at most 3 via display 39,
summed as in Proposition 13 over odd n from 3, with the tail of C1 from Lemma 14 and journal
Table 1 p. 1218, restricted to s at most 2 where h of s equals e^{-2}. Class HARD, a real
analytic induction step for Codex: displays 34 to 39 and the numerical bound on the sum of tau_n
over odd n at least 3 by 109. Strictly easier than the target: the n equal to one term is absent
and s is confined to the interval from 1 to 2. Non-vacuity: z equal to D equal to 2 gives s equal
to 1, and P empty satisfies every hypothesis. -/
theorem upper_stopping_odd_tail_low (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 2) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 3 ≤ n ∧ n % 2 = 1 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 109 * exp 2 * hS (log D / log z)) := by
  sorry

/-- LEAF: BJS Lemma 11 for odd n at least 3 via display 39, summed as in Proposition 13 over odd
n from 3, with the tail of C1 from Lemma 14 and journal Table 1 p. 1218, restricted to s from 2 to
3 where h of s equals e^{-s}. Class HARD, a real analytic induction step for Codex: displays 34 to
39, Lemma 10 for the integral of h, and the bound 109 on the sum of tau_n over odd n at least 3.
Strictly easier than the target: the n equal to one term is absent and s is confined to the
interval from 2 to 3. Non-vacuity: z equal to 2 and D equal to 4 gives s equal to 2, and P empty
satisfies every hypothesis. -/
theorem upper_stopping_odd_tail_high (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hs2 : 2 ≤ log D / log z) (hs : log D / log z ≤ 3) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 3 ≤ n ∧ n % 2 = 1 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 109 * exp 2 * hS (log D / log z)) := by
  sorry

/-- The target statement verbatim, from `first_stopping_bound` of Decomp327a, proved, and the
two LEAF tails. CONDITIONAL ON upper_stopping_odd_tail_low and upper_stopping_odd_tail_high. -/
theorem upper_stopping_error_split (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 3) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if n % 2 = 1 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) := by
  set S := siftingPrimes P z \ Q
  set V := ∏ p ∈ S, (1 - g p)
  set s := log D / log z with hsdef
  have hlz : 0 < log z := log_pos (by linarith)
  have hs1 : 1 ≤ s := by
    rw [hsdef, le_div_iff₀ hlz, one_mul]
    exact log_le_log (by linarith) hzD
  have hspos : 0 < s := by linarith
  rw [odd_sum_split _ (by omega)]
  have h1 : stoppingTerm S D g 1 ≤ V * (3 / s - 1 + (1 / 8349 : ℝ) * 3 * exp 2 * hS s) :=
    first_stopping_bound P Q g z D hP hg hz hprod hzD hs
  have hd1 : delayTerm 1 s = 3 / s - 1 := by
    simp only [delayTerm]
    rw [max_eq_left (by linarith)]
    field_simp
  have htail : (∑ n ∈ range (S.card + 3),
      if 3 ≤ n ∧ n % 2 = 1 then stoppingTerm S D g n - V * delayTerm n s else 0) ≤
      V * ((1 / 8349 : ℝ) * 109 * exp 2 * hS s) := by
    rcases le_total s 2 with h2 | h2
    · exact upper_stopping_odd_tail_low P Q g z D hP hg hz hprod hzD h2
    · exact upper_stopping_odd_tail_high P Q g z D hP hg hz hprod h2 hs
  rw [hd1]
  have e1 : V * (3 / s - 1 + (1 / 8349 : ℝ) * 3 * exp 2 * hS s) =
      V * (3 / s - 1) + V * ((1 / 8349 : ℝ) * 3 * exp 2 * hS s) := by ring
  have e2 : V * ((1 / 8349 : ℝ) * 112 * exp 2 * hS s) =
      V * ((1 / 8349 : ℝ) * 3 * exp 2 * hS s) + V * ((1 / 8349 : ℝ) * 109 * exp 2 * hS s) := by
    ring
  linarith [h1, htail, e1, e2]

end

end LeanLab.BS2022GRH.Decomp327b

#print axioms LeanLab.BS2022GRH.Decomp327b.upper_stopping_odd_tail_low
#print axioms LeanLab.BS2022GRH.Decomp327b.upper_stopping_odd_tail_high
#print axioms LeanLab.BS2022GRH.Decomp327b.upper_stopping_error_split
