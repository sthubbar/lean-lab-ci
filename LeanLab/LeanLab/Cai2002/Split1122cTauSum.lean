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

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- LEAF: BJS Lemma 11, display 31, monotonicity of the recursion in ε: for
0 < ε ≤ 1/100000, τ_n(ε) ≤ τ_n(1/100000) for every n, since each ξ in the recursion is
κ + (γ + κ) ε + 2 γ cp / t + 2 cc / t and t ξ is increasing in t and ε.
Class MEDIUM: induction on n through the maxima. -/
theorem tau_mono_eps1122c (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (n : ℕ) :
    bjsTau306 bjsC306 ε n ≤ bjsTau306 bjsC306 (1 / 100000) n := by
  sorry

/-- LEAF: BJS Proposition 13, the finite part of the Table 1 computation at ε = 1/100000:
the partial sums of τ_n over odd n up to N ≤ 500 are at most 131.508; interval value of the
full sum to 500 is 131.5073810. Class HARD: certified evaluation of 500 recursive terms
with exp and max. -/
theorem tau_odd_le500_1122c (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 131.508 := by
  sorry

/-- LEAF: as tau_odd_le500_1122c over even n, bound 134.837; interval value 134.8362246.
Class HARD. -/
theorem tau_even_le500_1122c (N : ℕ) (hN : N ≤ 500) :
    ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 134.837 := by
  have h₁ : ∀ n : ℕ, 0 ≤ bjsTau306 bjsC306 (1 / 100000 : ℝ) n := by
    have h₁₀ : ∀ n : ℕ, 0 < bjsC306 n := by
      intro n
      exact bjsC306_pos n
    have h₁₁ : ∀ n : ℕ, 0 ≤ bjsTau306 bjsC306 (1 / 100000 : ℝ) n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        match n with
        | 0 =>
          simp [bjsTau306]
        | 1 =>
          simp [bjsTau306]
          <;> norm_num
        | k + 2 =>
          have h₂ := ih (k + 1) (by omega)
          have h₃ : 0 ≤ bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1) := h₂
          have h₄ : 0 < bjsC306 (k + 1) := h₁₀ (k + 1)
          have h₅ : 0 < bjsC306 (k + 2) := h₁₀ (k + 2)
          have h₆ : 0 ≤ (1 / 100000 : ℝ) := by norm_num
          simp only [bjsTau306] at *
          split_ifs <;>
          (try { positivity }) <;>
          (try {
            -- For the even case: t * max(...) where t ≥ 0 and each ξ term ≥ κ > 0
            have h₇ : 0 ≤ (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1) : ℝ) := by exact_mod_cast h₃
            have h₈ : 0 < (bjsC306 (k + 1) : ℝ) := by exact_mod_cast h₄
            have h₉ : 0 < (bjsC306 (k + 2) : ℝ) := by exact_mod_cast h₅
            have h₁₀ : 0 ≤ (bjsC306 (k + 1) : ℝ) ^ k := by positivity
            have h₁₁ : 0 ≤ (bjsC306 (k + 2) : ℝ) ^ (k + 1) := by positivity
            -- Each bjsXi306 term is κ + (γ+κ)ε + 2γ·cp/t + 2·cc/t ≥ κ > 0 (in Lean, division by 0 gives 0, so it's ≥ κ)
            have h₁₂ : 0 ≤ (1 : ℝ) := by norm_num
            have h₁₃ : 0 ≤ Real.exp 0.2 := Real.exp_pos 0.2 |>.le
            have h₁₄ : 0 ≤ Real.exp 0.4 := Real.exp_pos 0.4 |>.le
            have h₁₅ : 0 ≤ Real.exp 0.6 := Real.exp_pos 0.6 |>.le
            have h₁₆ : 0 ≤ Real.exp 0.8 := Real.exp_pos 0.8 |>.le
            have h₁₇ : 0 ≤ Real.exp 1 := Real.exp_pos 1 |>.le
            -- Use the fact that each ξ term is non-negative because κ > 0 and other terms are non-negative
            have h₁₈ : 0 ≤ bjsXi306 1 (0.9607 : ℝ) (1 / 100000 : ℝ) ((bjsC306 (k + 1) : ℝ) ^ k) ((bjsC306 (k + 2) : ℝ) ^ (k + 1)) (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1)) := by
              dsimp only [bjsXi306]
              positivity
            have h₁₉ : 0 ≤ bjsXi306 (Real.exp 0.2) (0.9557 : ℝ) (1 / 100000 : ℝ) ((bjsC306 (k + 1) : ℝ) ^ k) ((bjsC306 (k + 2) : ℝ) ^ (k + 1)) (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1)) := by
              dsimp only [bjsXi306]
              positivity
            have h₂₀ : 0 ≤ bjsXi306 (Real.exp 0.4) (0.9457 : ℝ) (1 / 100000 : ℝ) ((bjsC306 (k + 1) : ℝ) ^ k) ((bjsC306 (k + 2) : ℝ) ^ (k + 1)) (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1)) := by
              dsimp only [bjsXi306]
              positivity
            have h₂₁ : 0 ≤ bjsXi306 (Real.exp 0.6) (0.9261 : ℝ) (1 / 100000 : ℝ) ((bjsC306 (k + 1) : ℝ) ^ k) ((bjsC306 (k + 2) : ℝ) ^ (k + 1)) (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1)) := by
              dsimp only [bjsXi306]
              positivity
            have h₂₂ : 0 ≤ bjsXi306 (Real.exp 0.8) (0.8914 : ℝ) (1 / 100000 : ℝ) ((bjsC306 (k + 1) : ℝ) ^ k) ((bjsC306 (k + 2) : ℝ) ^ (k + 1)) (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1)) := by
              dsimp only [bjsXi306]
              positivity
            have h₂₃ : 0 ≤ bjsXi306 (4 * Real.exp 1 / 3) (0.8349 : ℝ) (1 / 100000 : ℝ) ((bjsC306 (k + 1) : ℝ) ^ k) ((bjsC306 (k + 2) : ℝ) ^ (k + 1)) (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1)) := by
              dsimp only [bjsXi306]
              positivity
            -- The max of non-negative numbers is non-negative
            positivity
          }) <;>
          (try {
            -- For the odd case: t * max(ξ₃, ξ_tilde)
            have h₇ : 0 ≤ (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1) : ℝ) := by exact_mod_cast h₃
            have h₈ : 0 < (bjsC306 (k + 1) : ℝ) := by exact_mod_cast h₄
            have h₉ : 0 < (bjsC306 (k + 2) : ℝ) := by exact_mod_cast h₅
            have h₁₀ : 0 ≤ (bjsC306 (k + 1) : ℝ) ^ k := by positivity
            have h₁₁ : 0 ≤ (bjsC306 (k + 2) : ℝ) ^ (k + 1) := by positivity
            have h₁₂ : 0 ≤ Real.exp 1 := Real.exp_pos 1 |>.le
            have h₁₃ : 0 ≤ bjsXi306 (4 * Real.exp 1 / 3) (0.8349 : ℝ) (1 / 100000 : ℝ) ((bjsC306 (k + 1) : ℝ) ^ k) ((bjsC306 (k + 2) : ℝ) ^ (k + 1)) (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1)) := by
              dsimp only [bjsXi306]
              positivity
            have h₁₄ : 0 ≤ (0.9214 : ℝ) + (5 + 4 * (1 / 100000 : ℝ)) * (1 / 100000 : ℝ) + 6 * (1 + (1 / 100000 : ℝ)) * ((bjsC306 (k + 1) : ℝ) ^ k) / (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1)) + 2 * (2 + (1 / 100000 : ℝ)) * ((bjsC306 (k + 2) : ℝ) ^ (k + 1)) / (bjsTau306 bjsC306 (1 / 100000 : ℝ) (k + 1)) := by
              positivity
            positivity
          })
    exact h₁₁
  have h₂ : ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 (1 / 100000 : ℝ) n ≤ ∑ n ∈ (Finset.Icc 1 500).filter Even, bjsTau306 bjsC306 (1 / 100000 : ℝ) n := by sorry
  have h₃ : ∑ n ∈ (Finset.Icc 1 500).filter Even, bjsTau306 bjsC306 (1 / 100000 : ℝ) n ≤ 134.837 := by
    -- Rational upper bounds for exp values using Taylor series with remainder
    have h_exp_0_2 : Real.exp 0.2 ≤ (1221403 : ℝ) / 1000000 := by sorry
    have h_exp_0_4 : Real.exp 0.4 ≤ (1491825 : ℝ) / 1000000 := by sorry
    have h_exp_0_6 : Real.exp 0.6 ≤ (1822119 : ℝ) / 1000000 := by sorry
    have h_exp_0_8 : Real.exp 0.8 ≤ (2225541 : ℝ) / 1000000 := by sorry
    have h_exp_1 : Real.exp 1 ≤ (2718282 : ℝ) / 1000000 := by
      have := Real.exp_one_lt_d9
      norm_num at this ⊢
      <;> linarith
    have h_exp_4_3 : (4 : ℝ) * Real.exp 1 / 3 ≤ (3624376 : ℝ) / 1000000 := by
      have h₁ : Real.exp 1 ≤ (2718282 : ℝ) / 1000000 := h_exp_1
      have h₂ : (4 : ℝ) * Real.exp 1 / 3 ≤ (4 : ℝ) * ((2718282 : ℝ) / 1000000) / 3 := by
        gcongr
      norm_num at h₂ ⊢
      <;> linarith
    -- Define rational shadow sequence and prove it upper bounds the real sequence
    have h_main : ∑ n ∈ (Finset.Icc 1 500).filter Even, bjsTau306 bjsC306 (1 / 100000 : ℝ) n ≤ 134.837 := by sorry
    exact h_main
  linarith

/-- LEAF: the tail of the Table 1 computation at ε = 1/100000: for n > 500, c_n = 0.9607
and τ_n = κ' τ_(n-1) + O(0.9607 ^ n) with κ' < 1, so the sum of τ_n over odd n from 501 to
N is at most 0.49; interval value of the whole tail about 3.1e-6. Class MEDIUM: a
geometric bound from the recursion, after one certified value at n = 500. -/
theorem tau_odd_tail1122c (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Odd, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.49 := by
  sorry

/-- LEAF: as tau_odd_tail1122c over even n, bound 0.16. Class MEDIUM. -/
theorem tau_even_tail1122c (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 500 N).filter Even, bjsTau306 bjsC306 (1 / 100000) n ≤ 0.16 := by
  sorry

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
#print axioms LeanLab.Cai2002.tau_odd_sum_le132_twin1122c
#print axioms LeanLab.Cai2002.tau_even_sum_le135_twin1122c
