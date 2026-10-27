/-
P0042 GvLtR 1989 ratio check, window 15, even n in [28720002, 30700000], least Goldbach prime at most 797.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_28 : wem 28719205 28720002 30700000 &&& gm (wpm 28719205 1980795) (P10k.take 139) = wem 28719205 28720002 30700000 := by
  decide +kernel

theorem bnd_28 : MinGBBound 28720002 30700000 797 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 139 797 (by decide)) chk_28

theorem lr_28 : (17 + 173103/1000000 : ℝ) ≤ Real.log ((28720002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((28720002 : ℕ) : ℝ)) 17 (f := (173103/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_28 : (2 + 843343/1000000 : ℝ) ≤ Real.log (17 + 173103/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 173103/1000000 : ℝ)) 2 (f := (843343/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_28 : ∀ n, Even n → 28720002 ≤ n → n ≤ 30700000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_28 ls_28 (by norm_num) (by norm_num) bnd_28

theorem r2_28 : ∀ n, Even n → 28720002 ≤ n → n ≤ 30700000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_28 ls_28 (by norm_num) (by norm_num) bnd_28

end LeanLab.GvLtR1989
