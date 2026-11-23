/-
Twin route for the two blocked T bounds leaf306_T_odd_bound and leaf306_T_even_bound of
Split306Theorem6.lean, Bordignon, Johnston and Starichkova, arXiv 2207.09452v6,
papers/P0009.pdf, Proposition 13 with Table 1, pages 4 and 10 to 14.
The printed proof reaches the T bounds through display 31 summed over n, and S61 and S71
found that the sums of τ_n do not reach the Table 1 constants C_1 = 106 and C_2 = 107 at
ε = 1/100000; recomputed sums are 131.5074 over odd n and 134.8362 over even n, so Table 1
is not used here. This file states the T bounds for the row ε ≤ 1/100000 with the
recomputed constants 132 and 135, proved from tau_T_odd_bound306 and tau_T_even_bound306
and two numerical LEAFs, the partial sums of τ_n.
With c_33 = 0.70 in place of Table 2's 0.69, see notes/burst-20261122/Cai2002-lemma7grid.md,
the sums become 131.5076 and 134.8364, still below 132 and 135.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split306Theorem6

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- LEAF: BJS Proposition 13, page 14, the sum of the bounds τ_n of display 31 over odd n,
recomputed: for 0 < ε ≤ 1/100000 every partial sum over odd n of τ_n, with c_n of Table 2,
is at most 132. Interval arithmetic at 40 digits gives 131.50738 at ε = 1/100000, the sum
being increasing in ε, with tail beyond n = 3000 about 1e-48.
Class HARD: a certified evaluation of 500 recursive terms with exp and max, plus a geometric
tail bound beyond n = 500 where c_n = 0.9607. -/
theorem tau_odd_sum_le132_1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤ 132 := by
  sorry

/-- LEAF: BJS Proposition 13, page 14, the sum of the bounds τ_n of display 31 over even n,
recomputed: for 0 < ε ≤ 1/100000 every partial sum over even n of τ_n is at most 135.
Interval arithmetic gives 134.83623 at ε = 1/100000.
Class HARD: as tau_odd_sum_le132_1122c. -/
theorem tau_even_sum_le135_1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤ 135 := by
  sorry

/-- Twin of leaf306_T_odd_bound for the row ε ≤ 1/100000 with the recomputed constant 132 in
place of Table 1's C_1 = 106. CONDITIONAL ON tau_odd_sum_le132_1122c and on the LEAFs under
tau_T_odd_bound306. -/
theorem T_odd_bound132_1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (D : ℝ) (hD : z ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (F (log D / log z) - 1 +
          ε * 132 * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) :=
  tau_T_odd_bound306 F f hF ε hε P hP z hz g hg hgp K hK1 hKε h29 132
    (tau_odd_sum_le132_1122c ε hε hε5) D hD

/-- Twin of leaf306_T_even_bound for the row ε ≤ 1/100000 with the recomputed constant 135 in
place of Table 1's C_2 = 107. CONDITIONAL ON tau_even_sum_le135_1122c and on the LEAFs under
tau_T_even_bound306. -/
theorem T_even_bound135_1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (D : ℝ) (hD : z ^ 2 ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (1 - f (log D / log z) +
          ε * 135 * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) :=
  tau_T_even_bound306 F f hF ε hε P hP z hz g hg hgp K hK1 hKε h29 135
    (tau_even_sum_le135_1122c ε hε hε5) D hD

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.T_odd_bound132_1122c
#print axioms LeanLab.Cai2002.T_even_bound135_1122c
