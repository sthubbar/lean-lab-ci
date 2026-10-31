/-
P0042 GvLtR 1989 ratio check, window 51, even n in [100000002, 101980000], least Goldbach prime at most 1039.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_64 : wem 99998963 100000002 101980000 &&& gm (wpm2 99998963 1981037) (P10k.take 175) = wem 99998963 100000002 101980000 := by
  decide +kernel

theorem bnd_64 : MinGBBound 100000002 101980000 1039 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 175 1039 (by decide)) chk_64

theorem lr_64 : (18 + 420679/1000000 : ℝ) ≤ Real.log ((100000002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((100000002 : ℕ) : ℝ)) 18 (f := (420679/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_64 : (2 + 14273/15625 : ℝ) ≤ Real.log (18 + 420679/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 420679/1000000 : ℝ)) 2 (f := (14273/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_64 : ∀ n, Even n → 100000002 ≤ n → n ≤ 101980000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_64 ls_64 (by norm_num) (by norm_num) bnd_64

theorem r2_64 : ∀ n, Even n → 100000002 ≤ n → n ≤ 101980000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_64 ls_64 (by norm_num) (by norm_num) bnd_64

end LeanLab.GvLtR1989
