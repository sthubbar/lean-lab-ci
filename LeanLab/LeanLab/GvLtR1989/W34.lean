/-
P0042 GvLtR 1989 ratio check, window 34, even n in [66340002, 68320000], least Goldbach prime at most 811.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_47 : wem 66339191 66340002 68320000 &&& gm (wpm 66339191 1980809) (P10k.take 141) = wem 66339191 66340002 68320000 := by
  decide +kernel

theorem bnd_47 : MinGBBound 66340002 68320000 811 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 141 811 (by decide)) chk_47

theorem lr_47 : (18 + 5151/500000 : ℝ) ≤ Real.log ((66340002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((66340002 : ℕ) : ℝ)) 18 (f := (5151/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_47 : (2 + 445471/500000 : ℝ) ≤ Real.log (18 + 5151/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 5151/500000 : ℝ)) 2 (f := (445471/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_47 : ∀ n, Even n → 66340002 ≤ n → n ≤ 68320000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_47 ls_47 (by norm_num) (by norm_num) bnd_47

theorem r2_47 : ∀ n, Even n → 66340002 ≤ n → n ≤ 68320000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_47 ls_47 (by norm_num) (by norm_num) bnd_47

end LeanLab.GvLtR1989
