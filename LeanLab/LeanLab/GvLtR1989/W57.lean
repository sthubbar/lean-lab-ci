/-
P0042 GvLtR 1989 ratio check, window 57, even n in [111880002, 113860000], least Goldbach prime at most 1163.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_70 : wem 111878839 111880002 113860000 &&& gm (wpm2 111878839 1981161) (P10k.take 192) = wem 111878839 111880002 113860000 := by
  decide +kernel

theorem bnd_70 : MinGBBound 111880002 113860000 1163 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 192 1163 (by decide)) chk_70

theorem lr_70 : (18 + 66617/125000 : ℝ) ≤ Real.log ((111880002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((111880002 : ℕ) : ℝ)) 18 (f := (66617/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_70 : (2 + 229887/250000 : ℝ) ≤ Real.log (18 + 66617/125000 : ℝ) := by
  have h := le_log_of (x := (18 + 66617/125000 : ℝ)) 2 (f := (229887/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_70 : ∀ n, Even n → 111880002 ≤ n → n ≤ 113860000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_70 ls_70 (by norm_num) (by norm_num) bnd_70

theorem r2_70 : ∀ n, Even n → 111880002 ≤ n → n ≤ 113860000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_70 ls_70 (by norm_num) (by norm_num) bnd_70

end LeanLab.GvLtR1989
