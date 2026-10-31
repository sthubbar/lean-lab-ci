/-
P0042 GvLtR 1989 ratio check, window 11, even n in [20800002, 22780000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_24 : wem 20799179 20800002 22780000 &&& gm (wpm 20799179 1980821) (P10k.take 143) = wem 20799179 20800002 22780000 := by
  decide +kernel

theorem bnd_24 : MinGBBound 20800002 22780000 823 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_24

theorem lr_24 : (16 + 425231/500000 : ℝ) ≤ Real.log ((20800002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((20800002 : ℕ) : ℝ)) 16 (f := (425231/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_24 : (2 + 824377/1000000 : ℝ) ≤ Real.log (16 + 425231/500000 : ℝ) := by
  have h := le_log_of (x := (16 + 425231/500000 : ℝ)) 2 (f := (824377/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_24 : ∀ n, Even n → 20800002 ≤ n → n ≤ 22780000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_24 ls_24 (by norm_num) (by norm_num) bnd_24

theorem r2_24 : ∀ n, Even n → 20800002 ≤ n → n ≤ 22780000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_24 ls_24 (by norm_num) (by norm_num) bnd_24

end LeanLab.GvLtR1989
