/-
Final wiring of the T bound twins at 132 and 135, BJS arXiv 2207.09452v6 Proposition 13
with recomputed constants: the τ sums now use the PROVED monotonicity tau_mono_eps_s77 and
the tails tau_odd_tail_twin1122c and tau_even_tail_twin1122c, so the numeric inputs are
tau_odd_le500_1122c, tau_even_le500_1122c and tau500_value1122c. Proofs copied from
Wire1122cTauT.lean with these substitutions. No new LEAF and no new definition.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Wire1122cTauT
import LeanLab.Cai2002.Split1122cTauTail

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- The odd τ sum bound with the proved monotonicity and tail: rests on tau_odd_le500_1122c
and tau500_value1122c only. -/
theorem tau_odd_sum_final1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤ 132 := by
  have hm : ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤
      ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n :=
    Finset.sum_le_sum fun n _ => tau_mono_eps_s77 ε hε hε5 n
  refine hm.trans ?_
  rcases le_or_gt N 500 with h | h
  · linarith [tau_odd_le500_1122c N h]
  · rw [sum_split500_1122c Odd _ N h.le]
    linarith [tau_odd_le500_1122c 500 le_rfl, tau_odd_tail_twin1122c N]

/-- The even τ sum bound with the proved monotonicity and tail: rests on tau_even_le500_1122c
and tau500_value1122c only. -/
theorem tau_even_sum_final1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤ 135 := by
  have hm : ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤
      ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n :=
    Finset.sum_le_sum fun n _ => tau_mono_eps_s77 ε hε hε5 n
  refine hm.trans ?_
  rcases le_or_gt N 500 with h | h
  · linarith [tau_even_le500_1122c N h]
  · rw [sum_split500_1122c Even _ N h.le]
    linarith [tau_even_le500_1122c 500 le_rfl, tau_even_tail_twin1122c N]

/-- The T bound with 132, final wiring. -/
theorem T_odd_bound132_final1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
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
  tau_T_odd_bound_1122c F f hF ε hε P hP z hz g hg hgp K hK1 hKε h29 132
    (tau_odd_sum_final1122c ε hε hε5) D hD

/-- The T bound with 135, final wiring. -/
theorem T_even_bound135_final1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
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
  tau_T_even_bound_1122c F f hF ε hε P hP z hz g hg hgp K hK1 hKε h29 135
    (tau_even_sum_final1122c ε hε hε5) D hD

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.T_odd_bound132_final1122c
#print axioms LeanLab.Cai2002.T_even_bound135_final1122c
