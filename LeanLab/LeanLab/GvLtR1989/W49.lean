/-
P0042 GvLtR 1989 ratio check, window 49, even n in [96040002, 98020000], least Goldbach prime at most 919.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_62 : wem 96039083 96040002 98020000 &&& gm (wpm 96039083 1980917) (P10k.take 157) = wem 96039083 96040002 98020000 := by
  decide +kernel

theorem bnd_62 : MinGBBound 96040002 98020000 919 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 157 919 (by decide)) chk_62

theorem lr_62 : (18 + 190137/500000 : ℝ) ≤ Real.log ((96040002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((96040002 : ℕ) : ℝ)) 18 (f := (190137/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_62 : (2 + 911277/1000000 : ℝ) ≤ Real.log (18 + 190137/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 190137/500000 : ℝ)) 2 (f := (911277/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_62 : ∀ n, Even n → 96040002 ≤ n → n ≤ 98020000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_62 ls_62 (by norm_num) (by norm_num) bnd_62

theorem r2_62 : ∀ n, Even n → 96040002 ≤ n → n ≤ 98020000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_62 ls_62 (by norm_num) (by norm_num) bnd_62

end LeanLab.GvLtR1989
