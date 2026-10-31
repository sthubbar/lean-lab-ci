/-
P0042 GvLtR 1989 ratio check, window 29, even n in [56440002, 58420000], least Goldbach prime at most 809.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_42 : wem 56439193 56440002 58420000 &&& gm (wpm 56439193 1980807) (P10k.take 140) = wem 56439193 56440002 58420000 := by
  decide +kernel

theorem bnd_42 : MinGBBound 56440002 58420000 809 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 140 809 (by decide)) chk_42

theorem lr_42 : (17 + 848687/1000000 : ℝ) ≤ Real.log ((56440002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((56440002 : ℕ) : ℝ)) 17 (f := (848687/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_42 : (2 + 110241/125000 : ℝ) ≤ Real.log (17 + 848687/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 848687/1000000 : ℝ)) 2 (f := (110241/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_42 : ∀ n, Even n → 56440002 ≤ n → n ≤ 58420000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_42 ls_42 (by norm_num) (by norm_num) bnd_42

theorem r2_42 : ∀ n, Even n → 56440002 ≤ n → n ≤ 58420000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_42 ls_42 (by norm_num) (by norm_num) bnd_42

end LeanLab.GvLtR1989
