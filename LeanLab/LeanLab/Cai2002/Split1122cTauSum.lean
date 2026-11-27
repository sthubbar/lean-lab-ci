/-
Split of the two numerical LEAFs tau_odd_sum_le132_1122c and tau_even_sum_le135_1122c of
Split1122cTwinT.lean: the partial sums of the bounds τ_n of BJS display 31, Bordignon,
Johnston and Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, Lemma 11 and
Proposition 13, pages 11 to 14, with c_n of Table 2, at 0 < ε ≤ 1/100000.
The computation behind Table 1 has three parts, each a LEAF here:
* τ_n is increasing in ε, since t ξ = t κ + t (γ + κ) ε + 2 γ c_(n-1) ^ (n-2) + 2 c_n ^ (n-1)
  is increasing in t and in ε, so ε = 1/100000 is the worst case;
* the finite sums up to n = 500 at ε = 1/100000, interval values 131.5073810 over odd n and
  134.8362246 over even n;
* the tail beyond n = 500, where c_n = 0.9607 and τ_n decays geometrically, interval value
  about 3.1e-6 in total.
The two old LEAFs are proved here from these, as twins.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122cTwinT
import LeanLab.Cai2002.Prove1122cTauNum
import LeanLab.Cai2002.Prove1122cTauSumClose

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- LEAF: BJS Lemma 11, display 31, monotonicity of the recursion in ε: for
0 < ε ≤ 1/100000, τ_n(ε) ≤ τ_n(1/100000) for every n, since each ξ in the recursion is
κ + (γ + κ) ε + 2 γ cp / t + 2 cc / t and t ξ is increasing in t and ε.
Class MEDIUM: induction on n through the maxima.
PROVED in burst-20261124 S9 from tau_mono_eps_e1 of Prove1122cTauSumClose.lean. -/
theorem tau_mono_eps1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (n : ℕ) :
    bjsTau306 bjsC306 ε n ≤ bjsTau306 bjsC306 (1 / 100000) n := by
  exact tau_mono_eps_e1 ε hε hε5 n

/-- LEAF: BJS Proposition 13, the finite part of the Table 1 computation at ε = 1/100000:
the partial sums of τ_n over odd n up to N ≤ 500 are at most 131.508; interval value of the
full sum to 500 is 131.5073810. Class HARD: certified evaluation of 500 recursive terms
with exp and max.
PROVED in burst-20261124 S9 from tau_odd_le500_1122e of Prove1122cTauNum.lean, a certified
integer table checked by decide +kernel. -/
theorem tau_odd_le500_1122c (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 131.508 := by
  exact tau_odd_le500_1122e N hN

/-- LEAF: as tau_odd_le500_1122c over even n, bound 134.837; interval value 134.8362246.
Class HARD.
PROVED in burst-20261124 S9 from tau_even_le500_1122e of Prove1122cTauNum.lean. -/
theorem tau_even_le500_1122c (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 134.837 := by
  exact tau_even_le500_1122e N hN

/-- LEAF: the tail of the Table 1 computation at ε = 1/100000: for n > 500, c_n = 0.9607
and τ_n = κ' τ_(n-1) + O(0.9607 ^ n) with κ' < 1, so the sum of τ_n over odd n from 501 to
N is at most 0.49; interval value of the whole tail about 3.1e-6. Class MEDIUM: a
geometric bound from the recursion, after one certified value at n = 500.
PROVED in burst-20261124 S9 from tau_odd_tail_e1 of Prove1122cTauSumClose.lean. -/
theorem tau_odd_tail1122c (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.49 := by
  exact tau_odd_tail_e1 N

/-- LEAF: as tau_odd_tail1122c over even n, bound 0.16. Class MEDIUM.
PROVED in burst-20261124 S9 from tau_even_tail_e1 of Prove1122cTauSumClose.lean. -/
theorem tau_even_tail1122c (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.16 := by
  exact tau_even_tail_e1 N

/-- Splitting a filtered sum over Icc 1 N at 500. -/
theorem sum_split500_1122c (p : ℕ → Prop) [DecidablePred p] (u : ℕ → ℝ) (N : ℕ)
    (hN : 500 ≤ N) :
    ∑ n ∈ (Finset.Icc 1 N).filter p, u n =
      ∑ n ∈ (Finset.Icc 1 500).filter p, u n + ∑ n ∈ (Finset.Ioc 500 N).filter p, u n := by
  have h1 : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := fun M => by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h1, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_consecutive _ (Nat.zero_le 500) hN]

/-- Twin of tau_odd_sum_le132_1122c, statement verbatim, from the LEAFs above. -/
theorem tau_odd_sum_le132_twin1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤ 132 := by
  have hm : ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤
      ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n :=
    Finset.sum_le_sum fun n _ => tau_mono_eps1122c ε hε hε5 n
  refine hm.trans ?_
  rcases le_or_gt N 500 with h | h
  · linarith [tau_odd_le500_1122c N h]
  · rw [sum_split500_1122c Odd _ N h.le]
    linarith [tau_odd_le500_1122c 500 le_rfl, tau_odd_tail1122c N]

/-- Twin of tau_even_sum_le135_1122c, statement verbatim, from the LEAFs above. -/
theorem tau_even_sum_le135_twin1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤ 135 := by
  have hm : ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤
      ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n :=
    Finset.sum_le_sum fun n _ => tau_mono_eps1122c ε hε hε5 n
  refine hm.trans ?_
  rcases le_or_gt N 500 with h | h
  · linarith [tau_even_le500_1122c N h]
  · rw [sum_split500_1122c Even _ N h.le]
    linarith [tau_even_le500_1122c 500 le_rfl, tau_even_tail1122c N]

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.sum_split500_1122c
#print axioms LeanLab.Cai2002.tau_mono_eps1122c
#print axioms LeanLab.Cai2002.tau_odd_tail1122c
#print axioms LeanLab.Cai2002.tau_even_tail1122c
#print axioms LeanLab.Cai2002.tau_odd_le500_1122c
#print axioms LeanLab.Cai2002.tau_even_le500_1122c
#print axioms LeanLab.Cai2002.tau_odd_sum_le132_twin1122c
#print axioms LeanLab.Cai2002.tau_even_sum_le135_twin1122c
