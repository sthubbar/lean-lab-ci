/-
P0042 GvLtR 1989 ratio check, window 129, even n in [254440002, 256420000], least Goldbach prime at most 953.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_142 : wem 254439049 254440002 256420000 &&& gm (wpm2 254439049 1980951) (P10k.take 162) = wem 254439049 254440002 256420000 := by
  decide +kernel

theorem bnd_142 : MinGBBound 254440002 256420000 953 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 162 953 (by decide)) chk_142

theorem lr_142 : (19 + 177287/500000 : ℝ) ≤ Real.log ((254440002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((254440002 : ℕ) : ℝ)) 19 (f := (177287/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_142 : (2 + 962927/1000000 : ℝ) ≤ Real.log (19 + 177287/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 177287/500000 : ℝ)) 2 (f := (962927/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_142 : ∀ n, Even n → 254440002 ≤ n → n ≤ 256420000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_142 ls_142 (by norm_num) (by norm_num) bnd_142

theorem r2_142 : ∀ n, Even n → 254440002 ≤ n → n ≤ 256420000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_142 ls_142 (by norm_num) (by norm_num) bnd_142

end LeanLab.GvLtR1989
