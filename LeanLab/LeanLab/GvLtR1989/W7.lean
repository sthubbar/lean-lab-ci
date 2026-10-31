/-
P0042 GvLtR 1989 ratio check, window 7, even n in [12880002, 14860000], least Goldbach prime at most 751.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_20 : wem 12879251 12880002 14860000 &&& gm (wpm 12879251 1980749) (P10k.take 133) = wem 12879251 12880002 14860000 := by
  decide +kernel

theorem bnd_20 : MinGBBound 12880002 14860000 751 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 133 751 (by decide)) chk_20

theorem lr_20 : (16 + 74237/200000 : ℝ) ≤ Real.log ((12880002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((12880002 : ℕ) : ℝ)) 16 (f := (74237/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_20 : (2 + 795521/1000000 : ℝ) ≤ Real.log (16 + 74237/200000 : ℝ) := by
  have h := le_log_of (x := (16 + 74237/200000 : ℝ)) 2 (f := (795521/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_20 : ∀ n, Even n → 12880002 ≤ n → n ≤ 14860000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_20 ls_20 (by norm_num) (by norm_num) bnd_20

theorem r2_20 : ∀ n, Even n → 12880002 ≤ n → n ≤ 14860000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_20 ls_20 (by norm_num) (by norm_num) bnd_20

end LeanLab.GvLtR1989
