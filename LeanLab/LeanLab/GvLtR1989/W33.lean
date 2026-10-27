/-
P0042 GvLtR 1989 ratio check, window 33, even n in [64360002, 66340000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_46 : wem 64359179 64360002 66340000 &&& gm (wpm 64359179 1980821) (P10k.take 143) = wem 64359179 64360002 66340000 := by
  decide +kernel

theorem bnd_46 : MinGBBound 64360002 66340000 823 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_46

theorem lr_46 : (17 + 980001/1000000 : ℝ) ≤ Real.log ((64360002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((64360002 : ℕ) : ℝ)) 17 (f := (980001/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_46 : (2 + 889259/1000000 : ℝ) ≤ Real.log (17 + 980001/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 980001/1000000 : ℝ)) 2 (f := (889259/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_46 : ∀ n, Even n → 64360002 ≤ n → n ≤ 66340000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_46 ls_46 (by norm_num) (by norm_num) bnd_46

theorem r2_46 : ∀ n, Even n → 64360002 ≤ n → n ≤ 66340000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_46 ls_46 (by norm_num) (by norm_num) bnd_46

end LeanLab.GvLtR1989
