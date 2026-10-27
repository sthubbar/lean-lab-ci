/-
P0042 GvLtR 1989 ratio check, window 81, even n in [159400002, 161380000], least Goldbach prime at most 919.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_94 : wem 159399083 159400002 161380000 &&& gm (wpm2 159399083 1980917) (P10k.take 157) = wem 159399083 159400002 161380000 := by
  decide +kernel

theorem bnd_94 : MinGBBound 159400002 161380000 919 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 157 919 (by decide)) chk_94

theorem lr_94 : (18 + 443463/500000 : ℝ) ≤ Real.log ((159400002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((159400002 : ℕ) : ℝ)) 18 (f := (443463/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_94 : (2 + 234617/250000 : ℝ) ≤ Real.log (18 + 443463/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 443463/500000 : ℝ)) 2 (f := (234617/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_94 : ∀ n, Even n → 159400002 ≤ n → n ≤ 161380000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_94 ls_94 (by norm_num) (by norm_num) bnd_94

theorem r2_94 : ∀ n, Even n → 159400002 ≤ n → n ≤ 161380000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_94 ls_94 (by norm_num) (by norm_num) bnd_94

end LeanLab.GvLtR1989
