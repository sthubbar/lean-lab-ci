import LeanLab.ChenExplicit.H78X21775
import LeanLab.ChenExplicit.H78X21776

/-!
# Verify1285: independent VERIFY of `H78X21775.chenPos_1775`, PC run 20261020T2004Z-7678, U-1285

Checks only, no new mathematics:
* the exact statement of `chenPos_1775` and `chenPos_1776`, and their axioms;
* nonvacuity of the cited input `Thm44At 17.75 (cA1775 c₄)`: its constant is above 7, so the
  hypothesis asserts `S(A, P(z)) > 7 · U_N N / log² N > 0`, a genuine sieve lower bound; it is not
  trivially true, and on its own it gives only `N − p` free of prime factors below `N^{1/8}`, which
  is not the conclusion;
* the Thm50At and Thm51At constants are positive, so those inputs are genuine upper bounds;
* `ChenPosAt` is monotone in `t`, so the 17.75 statement contains the earlier 18 statement.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

open Real

noncomputable section
namespace LeanLab.ChenExplicit.Verify1285

open LeanLab.ChenExplicit LeanLab.ChenExplicit.H781775

/-- `ChenPosAt` is monotone in the threshold. -/
theorem chenPosAt_mono {s t : ℝ} (h : s ≤ t) (hs : H781775.ChenPosAt s) : H781775.ChenPosAt t := by
  intro N hE hN
  exact hs N hE (lt_of_le_of_lt (exp_le_exp.mpr (exp_le_exp.mpr h)) hN)

/-- Nonvacuity of the Theorem 44 (a) input: `cA1775 c₄ N > 7` for every `N > exp(exp 17.75)`. -/
theorem cA1775_gt (c4 : ℝ) (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 12) (N : ℕ)
    (hN : exp (exp 17.75) < (N : ℝ)) : 7 < cA1775 c4 N := by
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : exp 17.75 < Real.log N := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL' : (5.09 * 10 ^ 7 : ℝ) ≤ Real.log N := by have := expT_ge; linarith
  have h := cAa_ge H781775.gE twinC c4 (Real.log N) Section9.g_ge Section9.g_le twinC_ge_0654 hc4 hL'
  have hg : (1.781 : ℝ) ≤ H781775.gE := Section9.g_ge
  unfold cA1775
  have : (7 : ℝ) < 8 * (1 - 1 / 10 ^ 13) * (0.5490705 * H781775.gE - 108 * H781775.ε * 0.10253 - 1 / 10 ^ 11) := by
    norm_num [H781775.ε]; linarith
  linarith

/-- The Theorem 51 constant is positive, so `Thm51At 17.75 cB1775` is a genuine upper bound. -/
theorem cB1775_pos (N : ℕ) (hN : exp (exp 17.75) < (N : ℝ)) : 0 < cB1775 N := by
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : exp 17.75 < Real.log N := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL0 : 0 < Real.log N := lt_trans (exp_pos _) hL
  have hT : (0.654 : ℝ) ≤ twinC := twinC_ge_0654
  have hgE : 0 < H781775.gE := exp_pos _
  have hcb : 0 ≤ BJS.cbar := by have h2 := BJS.cbar_gt; norm_num at h2 ⊢; linarith
  have hm := (m_le1775 vS (by norm_num) le_rfl).1
  have hle : 0 < log (1 + H781775.e0) := lt_of_lt_of_le (by norm_num) log1e0_ge
  have he0 : (0 : ℝ) < H781775.e0 := by norm_num [H781775.e0]
  have hal : (0 : ℝ) < 1 / 2 - H781775.α := by norm_num [H781775.α]
  have hε : (0 : ℝ) < H781775.ε := by norm_num [H781775.ε]
  have hl83 : 0 < log (8 / 3 : ℝ) := log_pos (by norm_num)
  have hh : 0 ≤ Section9.h (3 / 2 - 3 * H781775.α) := by
    unfold Section9.h; split_ifs <;> positivity
  have hL2 : 0 < Real.log N ^ 2 := pow_pos hL0 2
  unfold cB1775 cB
  refine add_pos_of_pos_of_nonneg
    (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (by norm_num)) ?_) ?_) ?_) ?_) ?_
  · have : 0 < 4.51 / Real.log N ^ 2 := div_pos (by norm_num) hL2
    linarith
  · exact add_pos_of_pos_of_nonneg (mul_pos (div_pos two_pos hal) hgE)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε.le) (by norm_num))
        (exp_pos 2).le) hh)
  · have : 0 < 9 / Real.log N := div_pos (by norm_num) hL0
    linarith
  · refine add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hcb (div_pos (by norm_num) hL2)) ?_
    refine mul_nonneg ?_ ?_
    · have : 0 < 64 / Real.log N ^ 2 := div_pos (by norm_num) hL2
      linarith
    · have h1 : 0 ≤ 10 * log (1 + H781775.e0) / Real.log N :=
        div_nonneg (mul_nonneg (by norm_num) hle.le) hL0.le
      have h2 : 0 < 27 / Real.log N ^ 2 := div_pos (by norm_num) hL2
      linarith
  · refine mul_nonneg (div_nonneg hgE.le (by linarith)) (add_nonneg ?_ ?_)
    · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm) (by linarith))
        (mul_nonneg (by norm_num) hle.le)
    · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg hL0.le 5))
        (mul_nonneg (exp_pos _).le hle.le)

/-- The 17.75 inputs give the earlier 18 statement too, by monotonicity. -/
example (hA : Thm44At 17.75 (cA1775 H78X21775.c4))
    (hQ : Thm50At 17.75 (cQ1775 (H78X21775.l1 gE) H78X21775.l)) (hB : Thm51At 17.75 cB1775) :
    H781775.ChenPosAt 18 :=
  chenPosAt_mono (by norm_num) (H78X21775.chenPos_1775 hA hQ hB)

end LeanLab.ChenExplicit.Verify1285

#check @LeanLab.ChenExplicit.H78X21775.chenPos_1775
#check @LeanLab.ChenExplicit.H78X21776.chenPos_1776
#print axioms LeanLab.ChenExplicit.H78X21775.chenPos_1775
#print axioms LeanLab.ChenExplicit.H78X21776.chenPos_1776
#print axioms LeanLab.ChenExplicit.H781775.chenPos1775_of_sieveBounds
#print axioms LeanLab.ChenExplicit.H781775.margin1775
#print axioms LeanLab.ChenExplicit.H781775.margin_a1775
#print axioms LeanLab.ChenExplicit.H781775.chenCount_gt1775
#print axioms LeanLab.ChenExplicit.H781775.twinC_ge_0654
#print axioms LeanLab.ChenExplicit.H781775.m_le1775
#print axioms LeanLab.ChenExplicit.H781775.u0cond_44_50
#print axioms LeanLab.ChenExplicit.H781775.u0cond_51
#print axioms LeanLab.ChenExplicit.H781775.ranges1775
#print axioms LeanLab.ChenExplicit.H78X21775.c4_bounds
#print axioms LeanLab.ChenExplicit.H78X21775.l_bounds
#print axioms LeanLab.ChenExplicit.H78X21775.l1_bounds
#print axioms LeanLab.ChenExplicit.chen_inequality
#print axioms LeanLab.ChenExplicit.Verify1285.chenPosAt_mono
#print axioms LeanLab.ChenExplicit.Verify1285.cA1775_gt
#print axioms LeanLab.ChenExplicit.Verify1285.cB1775_pos
