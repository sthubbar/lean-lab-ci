/-
P0042 GvLtR 1989 ratio check, window 88, even n in [173260002, 175240000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_101 : wem 173259179 173260002 175240000 &&& gm (wpm2 173259179 1980821) (P10k.take 143) = wem 173259179 173260002 175240000 := by
  decide +kernel

theorem bnd_101 : MinGBBound 173260002 175240000 823 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_101

theorem lr_101 : (18 + 485151/500000 : ℝ) ≤ Real.log ((173260002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((173260002 : ℕ) : ℝ)) 18 (f := (485151/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_101 : (2 + 942873/1000000 : ℝ) ≤ Real.log (18 + 485151/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 485151/500000 : ℝ)) 2 (f := (942873/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_101 : ∀ n, Even n → 173260002 ≤ n → n ≤ 175240000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_101 ls_101 (by norm_num) (by norm_num) bnd_101

theorem r2_101 : ∀ n, Even n → 173260002 ≤ n → n ≤ 175240000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_101 ls_101 (by norm_num) (by norm_num) bnd_101

end LeanLab.GvLtR1989
