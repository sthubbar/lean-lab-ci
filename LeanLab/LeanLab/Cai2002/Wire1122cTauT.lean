/-
Wiring of the T bound twin route of Split1122cTwinT.lean to the S77 twins: BJS displays 13
and 14, Nathanson Theorem 9.4, now come from leaf306_series_solve8_wired1122c, which has no
LEAF, instead of the LEAF leaf306_series_solve8; the tau sums come from the split of
Split1122cTauSum.lean. Bordignon, Johnston and Starichkova, arXiv 2207.09452v6,
papers/P0009.pdf, pages 6 and 10 to 14. The proofs of tau_T_odd_bound_1122c and
tau_T_even_bound_1122c are those of tau_T_odd_bound306 and tau_T_even_bound306 copied with
the display 13 and 14 twins. They remain CONDITIONAL ON leaf306_lemma11 and on
leaf306_display18, which uses BJS Lemma 7, suspected false at n = 33.
No new LEAF and no new definition.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Wire1122cSeries8
import LeanLab.Cai2002.Split1122cTauSum

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- Twin of leaf306_display13, statement verbatim, from the LEAF free series solution. -/
theorem leaf306_display13_1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (s : ℝ) (hs : 1 ≤ s) :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (F s - 1) := by
  obtain ⟨F', f', hF', h13, -⟩ := leaf306_series_solve8_wired1122c
  rw [(leaf306_unique8 F f F' f' hF hF' s (by linarith)).1]
  exact h13 s hs

/-- Twin of leaf306_display14, statement verbatim, from the LEAF free series solution. -/
theorem leaf306_display14_1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (s : ℝ) (hs : 2 ≤ s) :
    HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (1 - f s) := by
  obtain ⟨F', f', hF', -, h14⟩ := leaf306_series_solve8_wired1122c
  rw [(leaf306_unique8 F f F' f' hF hF' s (by linarith)).2]
  exact h14 s hs

/-- Copy of tau_T_odd_bound306 with leaf306_display13_1122c. -/
theorem tau_T_odd_bound_1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (ε : ℝ) (hε : 0 < ε)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (C : ℝ) (htau : ∀ N : ℕ,
      ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤ C)
    (D : ℝ) (hD : z ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (F (log D / log z) - 1 +
          ε * C * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  classical
  set s := log D / log z with hsdef
  have hlogz : 0 < log z := log_pos (by linarith)
  have hs1 : 1 ≤ s := by
    rw [hsdef, le_div_iff₀ hlogz, one_mul]; exact log_le_log (by linarith) hD
  have hV0 := V_nonneg306 P z g hgp
  have hh0 : 0 ≤ LeanLab.ChenExplicit.hSieve s := hSieve_nonneg306 s (by linarith)
  have hcpos : ∀ n, 0 < bjsC306 n := bjsC306_pos
  have hT : ∀ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact leaf306_lemma11 P hP z hz g hg hgp ε hε K hK1 hKε h29 bjsC306 hcpos
      (fun m hm s' hs' => leaf306_display18 m hm s' hs') n hn.1.1 D (by nlinarith) (Or.inl ⟨hn.2, hs1⟩)
  have hf : ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, bjsF306 n s ≤ F s - 1 := by
    rw [Finset.sum_filter]
    refine sum_le_hasSum _ (fun n _ => ?_) (leaf306_display13_1122c F f hF s hs1)
    split_ifs with ho
    · exact leaf306_fn_nonneg n s (Or.inl ⟨ho, hs1⟩)
    · exact le_refl 0
  have hτ := htau (LeanLab.ChenExplicit.primesBelowIn P z).card
  have hco : 0 ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
      LeanLab.ChenExplicit.hSieve s :=
    mul_nonneg (mul_nonneg (mul_nonneg hV0 hε.le) (exp_pos _).le) hh0
  calc _ ≤ ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) :=
        Finset.sum_le_sum hT
    _ = (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, bjsF306 n s +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, bjsTau306 bjsC306 ε n := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * (F s - 1) +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * C :=
        add_le_add (mul_le_mul_of_nonneg_left hf hV0) (mul_le_mul_of_nonneg_left hτ hco)
    _ = _ := by ring

/-- Copy of tau_T_even_bound306 with leaf306_display14_1122c. -/
theorem tau_T_even_bound_1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (ε : ℝ) (hε : 0 < ε)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (C : ℝ) (htau : ∀ N : ℕ,
      ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤ C)
    (D : ℝ) (hD : z ^ 2 ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (1 - f (log D / log z) +
          ε * C * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  classical
  set s := log D / log z with hsdef
  have hlogz : 0 < log z := log_pos (by linarith)
  have hs1 : 2 ≤ s := by
    rw [hsdef, le_div_iff₀ hlogz]
    have h2 : log (z ^ 2) ≤ log D := log_le_log (by positivity) hD
    rw [Real.log_pow] at h2; push_cast at h2; linarith
  have hV0 := V_nonneg306 P z g hgp
  have hh0 : 0 ≤ LeanLab.ChenExplicit.hSieve s := hSieve_nonneg306 s (by linarith)
  have hcpos : ∀ n, 0 < bjsC306 n := bjsC306_pos
  have hT : ∀ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact leaf306_lemma11 P hP z hz g hg hgp ε hε K hK1 hKε h29 bjsC306 hcpos
      (fun m hm s' hs' => leaf306_display18 m hm s' hs') n hn.1.1 D (by nlinarith) (Or.inr ⟨hn.2, hs1⟩)
  have hf : ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, bjsF306 n s ≤ 1 - f s := by
    rw [Finset.sum_filter]
    refine sum_le_hasSum _ (fun n _ => ?_) (leaf306_display14_1122c F f hF s hs1)
    split_ifs with ho
    · exact leaf306_fn_nonneg n s (Or.inr ⟨ho, hs1⟩)
    · exact le_refl 0
  have hτ := htau (LeanLab.ChenExplicit.primesBelowIn P z).card
  have hco : 0 ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
      LeanLab.ChenExplicit.hSieve s :=
    mul_nonneg (mul_nonneg (mul_nonneg hV0 hε.le) (exp_pos _).le) hh0
  calc _ ≤ ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) :=
        Finset.sum_le_sum hT
    _ = (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, bjsF306 n s +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, bjsTau306 bjsC306 ε n := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * (1 - f s) +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * C :=
        add_le_add (mul_le_mul_of_nonneg_left hf hV0) (mul_le_mul_of_nonneg_left hτ hco)
    _ = _ := by ring

/-- T_odd_bound132_1122c wired: the T bound with 132 through the twins above. -/
theorem T_odd_bound132_wired1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
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
    (tau_odd_sum_le132_twin1122c ε hε hε5) D hD

/-- T_even_bound135_1122c wired: the T bound with 135 through the twins above. -/
theorem T_even_bound135_wired1122c (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
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
    (tau_even_sum_le135_twin1122c ε hε hε5) D hD

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leaf306_display13_1122c
#print axioms LeanLab.Cai2002.T_odd_bound132_wired1122c
#print axioms LeanLab.Cai2002.T_even_bound135_wired1122c
