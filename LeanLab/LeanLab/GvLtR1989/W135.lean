/-
P0042 GvLtR 1989 ratio check, window 135, even n in [266320002, 268300000], least Goldbach prime at most 907.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_148 : wem 266319095 266320002 268300000 &&& gm (wpm2 266319095 1980905) (P10k.take 155) = wem 266319095 266320002 268300000 := by
  decide +kernel

theorem bnd_148 : MinGBBound 266320002 268300000 907 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 155 907 (by decide)) chk_148

theorem lr_148 : (19 + 25013/62500 : ℝ) ≤ Real.log ((266320002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((266320002 : ℕ) : ℝ)) 19 (f := (25013/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_148 : (2 + 482641/500000 : ℝ) ≤ Real.log (19 + 25013/62500 : ℝ) := by
  have h := le_log_of (x := (19 + 25013/62500 : ℝ)) 2 (f := (482641/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_148 : ∀ n, Even n → 266320002 ≤ n → n ≤ 268300000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_148 ls_148 (by norm_num) (by norm_num) bnd_148

theorem r2_148 : ∀ n, Even n → 266320002 ≤ n → n ≤ 268300000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_148 ls_148 (by norm_num) (by norm_num) bnd_148

end LeanLab.GvLtR1989
