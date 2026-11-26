/-
P0068 Zhan 1991, page 263 display (3.3): the coefficient LEAF `perron_coef_leaf_ps2` of
PerronSum1122d.lean, PROVED. Burst 20261124, session S9, unit A-extra-1. Under condition (3.5)
every `N_j ≥ 1/2` and `Π N_j ≤ N`, so `N₁ ≤ 2^19 N` and `n₁ ≤ 2N₁ ≤ 2^20 N`; the product of the
coefficients is at most `log n₁ ≤ 20 log 2 + log N ≤ (20 log 2 + 1/ε) N^ε`, since `|a_j| ≤ 1` for
`j ≥ 2` and `|χ| ≤ 1`. AI-written Lean code, Claude. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.PerronSum1122d

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The coefficients `a_j` of display (3.4), page 263, have `|a_j(n)| ≤ 1` for `j ≥ 2`. -/
theorem aj_norm_le_one_of_two_le_A2 (j n : ℕ) (hj : 2 ≤ j) : ‖aj j n‖ ≤ 1 := by
  unfold aj
  rw [if_neg (show ¬ j = 1 by omega)]
  split_ifs
  · simp
  · rw [show ((μ n : ℤ) : ℂ) = ((μ n : ℤ) : ℝ) by simp, Complex.norm_real, Real.norm_eq_abs,
      ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- The same statement as the LEAF `perron_coef_leaf_ps2`, page 263 display (3.3). -/
theorem perron_coef_proof_A2 : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ) (n : Fin 20 → ℕ), N₀ ≤ N → Cond35 N Nv →
    n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)) →
    ‖∏ j : Fin 20, aj (j.val + 1) (n j) * χ (n j)‖ ≤ K * (N : ℝ) ^ ε := by
  intro ε hε
  refine ⟨20 * Real.log 2 + 1 / ε, 1, by positivity, ?_⟩
  intro N q χ Nv n hN hC hn
  obtain ⟨hhalf, -, hprod, -⟩ := hC
  have hN1 : (1 : ℝ) ≤ N := hN
  have hmem : ∀ j, n j ∈ dyad (Nv j) := Fintype.mem_piFinset.mp hn
  -- the first variable
  have h0 := hmem 0
  simp only [dyad, Finset.mem_filter, Finset.mem_Icc] at h0
  obtain ⟨⟨h0a, h0b⟩, -⟩ := h0
  have hNv0 : 0 ≤ Nv 0 := le_trans (by norm_num) (hhalf 0)
  have hn0le : (n 0 : ℝ) ≤ 2 * Nv 0 := by
    have := Nat.floor_le (show 0 ≤ 2 * Nv 0 by positivity)
    exact le_trans (by exact_mod_cast h0b) this
  have hrest : ((1 : ℝ) / 2) ^ 19 ≤ ∏ i : Fin 19, Nv i.succ := by
    have : ∏ _i : Fin 19, ((1 : ℝ) / 2) ≤ ∏ i : Fin 19, Nv i.succ :=
      Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => hhalf i.succ)
    simpa using this
  have hsplit : ∏ j, Nv j = Nv 0 * ∏ i : Fin 19, Nv i.succ := Fin.prod_univ_succ _
  have hNv0le : Nv 0 ≤ 2 ^ 19 * N := by
    have h1 : Nv 0 * ((1 : ℝ) / 2) ^ 19 ≤ N := by
      calc Nv 0 * ((1 : ℝ) / 2) ^ 19 ≤ Nv 0 * ∏ i : Fin 19, Nv i.succ :=
            mul_le_mul_of_nonneg_left hrest hNv0
        _ = ∏ j, Nv j := hsplit.symm
        _ ≤ N := hprod
    have : ((1 : ℝ) / 2) ^ 19 * 2 ^ 19 = 1 := by norm_num
    nlinarith
  have hn0pos : (1 : ℝ) ≤ n 0 := by exact_mod_cast h0a
  have hn0big : (n 0 : ℝ) ≤ 2 ^ 20 * N := by nlinarith
  -- bound the norm of the product by log n₀
  have hnorm : ‖∏ j : Fin 20, aj (j.val + 1) (n j) * χ (n j)‖ ≤ Real.log (n 0) := by
    rw [norm_prod, Fin.prod_univ_succ]
    have hfirst : ‖aj ((0 : Fin 20).val + 1) (n 0) * χ (n 0)‖ ≤ Real.log (n 0) := by
      rw [norm_mul]
      have ha : ‖aj ((0 : Fin 20).val + 1) (n 0)‖ = Real.log (n 0) := by
        simp only [aj, Fin.val_zero, zero_add, ite_true]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn0pos)]
      rw [ha]
      calc Real.log (n 0) * ‖χ (n 0)‖ ≤ Real.log (n 0) * 1 :=
            mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _)
              (Real.log_nonneg hn0pos)
        _ = Real.log (n 0) := mul_one _
    have hothers : ∏ i : Fin 19, ‖aj ((i.succ : Fin 20).val + 1) (n i.succ) * χ (n i.succ)‖ ≤ 1 := by
      refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) ?_
      intro i _
      rw [norm_mul]
      have h1 := aj_norm_le_one_of_two_le_A2 ((i.succ : Fin 20).val + 1) (n i.succ)
        (by simp [Fin.val_succ])
      have h2 := DirichletCharacter.norm_le_one χ (n i.succ)
      exact mul_le_one₀ h1 (norm_nonneg _) h2
    calc _ ≤ Real.log (n 0) * 1 :=
          mul_le_mul hfirst hothers (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            (Real.log_nonneg hn0pos)
      _ = Real.log (n 0) := mul_one _
  refine le_trans hnorm ?_
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog1 : Real.log (n 0) ≤ Real.log (2 ^ 20 * N) :=
    Real.log_le_log (by linarith) hn0big
  rw [Real.log_mul (by norm_num) hNpos.ne', Real.log_pow] at hlog1
  have hlogN : Real.log N ≤ (N : ℝ) ^ ε / ε := Real.log_le_rpow_div hNpos.le hε
  have hNe : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have : (N : ℝ) ^ ε / ε = 1 / ε * (N : ℝ) ^ ε := by ring
  push_cast at hlog1
  nlinarith

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.aj_norm_le_one_of_two_le_A2
#print axioms LeanLab.Zhan1991.perron_coef_proof_A2
