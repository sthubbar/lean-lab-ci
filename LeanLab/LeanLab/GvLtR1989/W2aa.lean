/-
P0042 GvLtR 1989 ratio check, window 2aa, even n in [2980002, 3475000], least Goldbach prime at most 523.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_13 : wem 2979479 2980002 3475000 &&& gm (wpm 2979479 495521) (P10k.take 99) = wem 2979479 2980002 3475000 := by
  decide +kernel

theorem bnd_13 : MinGBBound 2980002 3475000 523 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 99 523 (by decide)) chk_13

theorem lr_13 : (14 + 907433/1000000 : ℝ) ≤ Real.log ((2980002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((2980002 : ℕ) : ℝ)) 14 (f := (907433/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_13 : (2 + 350929/500000 : ℝ) ≤ Real.log (14 + 907433/1000000 : ℝ) := by
  have h := le_log_of (x := (14 + 907433/1000000 : ℝ)) 2 (f := (350929/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_13 : ∀ n, Even n → 2980002 ≤ n → n ≤ 3475000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_13 ls_13 (by norm_num) (by norm_num) bnd_13

theorem r2_13 : ∀ n, Even n → 2980002 ≤ n → n ≤ 3475000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_13 ls_13 (by norm_num) (by norm_num) bnd_13

end LeanLab.GvLtR1989
