/-
P0042 GvLtR 1989 ratio check, window 133, even n in [262360002, 264340000], least Goldbach prime at most 907.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_146 : wem 262359095 262360002 264340000 &&& gm (wpm2 262359095 1980905) (P10k.take 155) = wem 262359095 262360002 264340000 := by
  decide +kernel

theorem bnd_146 : MinGBBound 262360002 264340000 907 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 155 907 (by decide)) chk_146

theorem lr_146 : (19 + 385227/1000000 : ℝ) ≤ Real.log ((262360002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((262360002 : ℕ) : ℝ)) 19 (f := (385227/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_146 : (2 + 96451/100000 : ℝ) ≤ Real.log (19 + 385227/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 385227/1000000 : ℝ)) 2 (f := (96451/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_146 : ∀ n, Even n → 262360002 ≤ n → n ≤ 264340000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_146 ls_146 (by norm_num) (by norm_num) bnd_146

theorem r2_146 : ∀ n, Even n → 262360002 ≤ n → n ≤ 264340000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_146 ls_146 (by norm_num) (by norm_num) bnd_146

end LeanLab.GvLtR1989
