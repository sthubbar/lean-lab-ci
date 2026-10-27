/-
P0042 GvLtR 1989 ratio check, window 10, even n in [18820002, 20800000], least Goldbach prime at most 733.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_23 : wem 18819269 18820002 20800000 &&& gm (wpm 18819269 1980731) (P10k.take 130) = wem 18819269 18820002 20800000 := by
  decide +kernel

theorem bnd_23 : MinGBBound 18820002 20800000 733 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 130 733 (by decide)) chk_23

theorem lr_23 : (16 + 750429/1000000 : ℝ) ≤ Real.log ((18820002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((18820002 : ℕ) : ℝ)) 16 (f := (750429/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_23 : (2 + 409211/500000 : ℝ) ≤ Real.log (16 + 750429/1000000 : ℝ) := by
  have h := le_log_of (x := (16 + 750429/1000000 : ℝ)) 2 (f := (409211/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_23 : ∀ n, Even n → 18820002 ≤ n → n ≤ 20800000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_23 ls_23 (by norm_num) (by norm_num) bnd_23

theorem r2_23 : ∀ n, Even n → 18820002 ≤ n → n ≤ 20800000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_23 ls_23 (by norm_num) (by norm_num) bnd_23

end LeanLab.GvLtR1989
