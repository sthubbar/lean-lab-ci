/-
P0042 GvLtR 1989 ratio check, window 150, even n in [296020002, 298000000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_163 : wem 296019179 296020002 298000000 &&& gm (wpm2 296019179 1980821) (P10k.take 143) = wem 296019179 296020002 298000000 := by
  decide +kernel

theorem bnd_163 : MinGBBound 296020002 298000000 823 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_163

theorem lr_163 : (19 + 31621/62500 : ℝ) ≤ Real.log ((296020002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((296020002 : ℕ) : ℝ)) 19 (f := (31621/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_163 : (2 + 970717/1000000 : ℝ) ≤ Real.log (19 + 31621/62500 : ℝ) := by
  have h := le_log_of (x := (19 + 31621/62500 : ℝ)) 2 (f := (970717/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_163 : ∀ n, Even n → 296020002 ≤ n → n ≤ 298000000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_163 ls_163 (by norm_num) (by norm_num) bnd_163

theorem r2_163 : ∀ n, Even n → 296020002 ≤ n → n ≤ 298000000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_163 ls_163 (by norm_num) (by norm_num) bnd_163

end LeanLab.GvLtR1989
