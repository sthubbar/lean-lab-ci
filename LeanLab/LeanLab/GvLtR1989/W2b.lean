/-
P0042 GvLtR 1989 ratio check, window 2b, even n in [3970002, 4960000], least Goldbach prime at most 607.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_15 : wem 3969395 3970002 4960000 &&& gm (wpm 3969395 990605) (P10k.take 111) = wem 3969395 3970002 4960000 := by
  decide +kernel

theorem bnd_15 : MinGBBound 3970002 4960000 607 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 111 607 (by decide)) chk_15

theorem lr_15 : (15 + 48569/250000 : ℝ) ≤ Real.log ((3970002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((3970002 : ℕ) : ℝ)) 15 (f := (48569/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_15 : (2 + 720917/1000000 : ℝ) ≤ Real.log (15 + 48569/250000 : ℝ) := by
  have h := le_log_of (x := (15 + 48569/250000 : ℝ)) 2 (f := (720917/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_15 : ∀ n, Even n → 3970002 ≤ n → n ≤ 4960000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_15 ls_15 (by norm_num) (by norm_num) bnd_15

theorem r2_15 : ∀ n, Even n → 3970002 ≤ n → n ≤ 4960000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_15 ls_15 (by norm_num) (by norm_num) bnd_15

end LeanLab.GvLtR1989
