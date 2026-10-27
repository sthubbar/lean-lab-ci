/-
P0042 GvLtR 1989 ratio check, window 71, even n in [139600002, 141580000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_84 : wem 139599179 139600002 141580000 &&& gm (wpm2 139599179 1980821) (P10k.take 143) = wem 139599179 139600002 141580000 := by
  decide +kernel

theorem bnd_84 : MinGBBound 139600002 141580000 823 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_84

theorem lr_84 : (18 + 75429/100000 : ℝ) ≤ Real.log ((139600002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((139600002 : ℕ) : ℝ)) 18 (f := (75429/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_84 : (2 + 931421/1000000 : ℝ) ≤ Real.log (18 + 75429/100000 : ℝ) := by
  have h := le_log_of (x := (18 + 75429/100000 : ℝ)) 2 (f := (931421/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_84 : ∀ n, Even n → 139600002 ≤ n → n ≤ 141580000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_84 ls_84 (by norm_num) (by norm_num) bnd_84

theorem r2_84 : ∀ n, Even n → 139600002 ≤ n → n ≤ 141580000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_84 ls_84 (by norm_num) (by norm_num) bnd_84

end LeanLab.GvLtR1989
